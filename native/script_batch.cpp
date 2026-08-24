// SPDX-License-Identifier: MIT
//
// Keep transaction script verification aligned with Bitcoin Core's
// ConnectBlock path. The public libbitcoinconsensus ABI is intentionally
// input-oriented; this bridge adds the transaction-oriented operation needed
// by the Rust validator without changing the underlying Core script engine.

#include <cstdint>
#include <cstring>
#include <ios>
#include <string>
#include <utility>
#include <vector>

#include "primitives/transaction.h"
#include "script/interpreter.h"
#include "serialize.h"

struct bitcoind_rs_utxo {
    const unsigned char* script_pubkey;
    unsigned int script_pubkey_len;
    std::int64_t value;
};

namespace {

// The bundled libbitcoinconsensus source uses this small bounded reader for
// its public ABI. Keep the same deserialization boundary without including
// streams.h, whose secure allocator helper is intentionally not shipped in
// the minimal dependency package.
class TxInputStream {
public:
    TxInputStream(int version, const unsigned char* data, size_t length)
        : m_version(version), m_data(data), m_remaining(length) {}

    void read(Span<std::byte> destination)
    {
        if (destination.size() > m_remaining || destination.data() == nullptr || m_data == nullptr) {
            throw std::ios_base::failure("TxInputStream: invalid read");
        }
        std::memcpy(destination.data(), m_data, destination.size());
        m_remaining -= destination.size();
        m_data += destination.size();
    }

    template <typename T>
    TxInputStream& operator>>(T&& value)
    {
        ::Unserialize(*this, value);
        return *this;
    }

    int GetVersion() const { return m_version; }

private:
    int m_version;
    const unsigned char* m_data;
    size_t m_remaining;
};

} // namespace

extern "C" int bitcoind_rs_verify_transaction_scripts(
    const unsigned char* transaction_bytes,
    unsigned int transaction_len,
    const bitcoind_rs_utxo* spent_outputs,
    unsigned int spent_outputs_len,
    unsigned int flags,
    unsigned int* failed_input)
{
    if (failed_input != nullptr) {
        *failed_input = 0;
    }
    if (transaction_bytes == nullptr && transaction_len != 0) {
        return -1;
    }

    try {
        TxInputStream stream(PROTOCOL_VERSION, transaction_bytes, transaction_len);
        CTransaction transaction(deserialize, stream);
        if (GetSerializeSize(transaction, PROTOCOL_VERSION) != transaction_len) {
            return -1;
        }
        if (spent_outputs_len != transaction.vin.size() ||
            (spent_outputs == nullptr && spent_outputs_len != 0)) {
            return -1;
        }

        std::vector<CTxOut> outputs;
        outputs.reserve(spent_outputs_len);
        for (unsigned int index = 0; index < spent_outputs_len; ++index) {
            const bitcoind_rs_utxo& spent = spent_outputs[index];
            if (spent.script_pubkey == nullptr && spent.script_pubkey_len != 0) {
                return -1;
            }
            outputs.emplace_back(
                CAmount(spent.value),
                CScript(spent.script_pubkey, spent.script_pubkey + spent.script_pubkey_len));
        }

        // This is the same lifetime and initialization pattern used by Core's
        // CScriptCheck objects: every input of one transaction shares these
        // precomputed BIP143/BIP341 hashes and spent-output metadata.
        PrecomputedTransactionData txdata(transaction);
        if ((flags & SCRIPT_VERIFY_TAPROOT) != 0) {
            txdata.Init(transaction, std::move(outputs));
        }

        for (unsigned int input = 0; input < transaction.vin.size(); ++input) {
            const CTxOut& output = txdata.m_spent_outputs_ready
                ? txdata.m_spent_outputs[input]
                : outputs[input];
            TransactionSignatureChecker checker(
                &transaction,
                input,
                output.nValue,
                txdata,
                MissingDataBehavior::FAIL);
            ScriptError error = SCRIPT_ERR_UNKNOWN_ERROR;
            if (!VerifyScript(
                    transaction.vin[input].scriptSig,
                    output.scriptPubKey,
                    &transaction.vin[input].scriptWitness,
                    flags,
                    checker,
                    &error)) {
                if (failed_input != nullptr) {
                    *failed_input = input;
                }
                return 0;
            }
        }
        return 1;
    } catch (...) {
        return -1;
    }
}
