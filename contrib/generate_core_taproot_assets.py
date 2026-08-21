#!/usr/bin/env python3
"""Generate script-verification vectors from Bitcoin Core's Taproot tests."""

import argparse
import json
import random
import sys
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "core_checkout",
        type=Path,
        help="path to a Bitcoin Core source checkout (v31.1 for the audit suite)",
    )
    parser.add_argument("output", type=Path, help="JSON asset path to create")
    arguments = parser.parse_args()

    functional_tests = arguments.core_checkout.resolve() / "test" / "functional"
    if not (functional_tests / "feature_taproot.py").is_file():
        parser.error(f"Bitcoin Core feature_taproot.py not found under {functional_tests}")
    sys.path.insert(0, str(functional_tests))

    import feature_taproot as tap  # pylint: disable=import-outside-toplevel
    from test_framework.messages import (  # pylint: disable=import-outside-toplevel
        COutPoint,
        CTransaction,
        CTxIn,
        CTxOut,
    )
    from test_framework.script import (  # pylint: disable=import-outside-toplevel
        CScript,
        OP_1,
    )

    random.seed(31_001)
    spenders = (
        tap.sample_spenders()
        + tap.spenders_taproot_active()
        + tap.spenders_taproot_nonstandard()
    )
    vectors = []

    for number, spender in enumerate(spenders):
        target_index = 1 if spender.need_vin_vout_mismatch else 0
        transaction = CTransaction()
        transaction.version = 2
        transaction.nLockTime = 100
        previous_outputs = []

        if target_index:
            transaction.vin.append(
                CTxIn(COutPoint(number * 2 + 1, 0), CScript(), 0xFFFFFFFE)
            )
            previous_outputs.append(CTxOut(200_000, CScript([OP_1])))

        transaction.vin.append(
            CTxIn(COutPoint(number * 2 + 2, 0), CScript(), 0xFFFFFFFE)
        )
        previous_outputs.append(CTxOut(1_000_000, spender.script))
        transaction.vout.append(
            CTxOut(
                sum(output.nValue for output in previous_outputs) - 50_000,
                CScript([OP_1]),
            )
        )

        success = spender.sat_function(
            transaction, target_index, previous_outputs, True
        )
        failure = (
            None
            if spender.no_fail
            else spender.sat_function(transaction, target_index, previous_outputs, False)
        )
        flags = (
            tap.LEGACY_FLAGS
            if spender.comment.startswith(("legacy/", "inactive/"))
            else tap.TAPROOT_FLAGS
        )

        def encode_satisfaction(value):
            if value is None:
                return None
            return {
                "scriptSig": bytes(value[0]).hex(),
                "witness": [bytes(item).hex() for item in value[1]],
            }

        vector = {
            "tx": transaction.serialize_without_witness().hex(),
            "prevouts": [output.serialize().hex() for output in previous_outputs],
            "index": target_index,
            "flags": flags,
            "comment": spender.comment,
            "success": encode_satisfaction(success),
        }
        if failure is not None:
            vector["failure"] = encode_satisfaction(failure)
        vectors.append(vector)

    arguments.output.write_text(
        json.dumps(vectors, separators=(",", ":")), encoding="utf-8"
    )
    print(f"generated {len(vectors)} vectors in {arguments.output}")


if __name__ == "__main__":
    main()
