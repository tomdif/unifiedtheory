#!/usr/bin/env python3
"""Full signed response on nested, charge-zero clock/neutral packet spans.

Uses the existing admitted packet family and complete eight-factor forms.
All complex modes are retained. Floating quadrature and eigenvalues do not
prove a uniform bound or a statement about evolution.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import numpy as np
import independent_neutral_response_probe as family
import projected_integrated_response_probe as baseline
import projected_kernel_matrix_probe as transverse
import matter_energy_gram_probe as old


LIMITS = [0, 4, 12, 24, 32]
PACKETS = [[10., B, -.4, 1., float(p)]
           for B in [7., 8., 9.] for p in range(-32, 33, 2)]
SETTINGS = [
    dict(nt=64, nd=512, left=-10., right=4., panels=96, order=14),
    dict(nt=96, nd=768, left=-12., right=4.5, panels=144, order=16),
]
PARENT = "data/quantum_full_time_spectrum_audit.json"
PARENT_SHA = "6931e5e3ee971108a12a4bcfeb44100bce3ae19e74a343d1cfaf858f410c8470"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_root_prefix(root, parent):
    lines = (root/"UnifiedTheory.lean").read_text().splitlines(keepends=True)
    assert hashlib.sha256("".join(lines[:7890]).encode()).hexdigest() == parent["root_check"]["source_sha256"]
    assert all(line.startswith("import ") and line.endswith("\n") for line in lines[7890:])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    np.seterr(over="raise", invalid="raise", divide="raise")
    root = Path(__file__).resolve().parents[1]
    assert sha(root/PARENT) == PARENT_SHA
    parent = json.loads((root/PARENT).read_text())
    assert all(sha(root/p) == h for p, h in parent["source_sha256"].items())
    check_root_prefix(root, parent)
    first, witnesses, runs = None, {}, []
    for setting in SETTINGS:
        start = time.monotonic()
        kernel = family.Response(PACKETS, h=.05, eps=1.,
                                 nt=setting["nt"], nd=setting["nd"])
        forms, checks = kernel.integrate(
            **{p: setting[p] for p in ["left", "right", "panels", "order"]})
        W, condition = old.whitening(forms["energy"])
        assert condition["whitening_residual"] < 2e-8
        changes = {} if first is None else {
            name: float(np.linalg.norm(W.conj().T@(M-first[name])@W, 2)/
                        max(1., np.linalg.norm(W.conj().T@M@W, 2)))
            for name, M in forms.items()}
        assert not changes or max(changes.values()) < 2e-8, changes
        spaces = []
        for limit in LIMITS:
            ids = [i for i, p in enumerate(PACKETS) if abs(p[4]) <= limit]
            sub = {name: M[np.ix_(ids, ids)] for name, M in forms.items()}
            spectrum = baseline.spectrum(sub)
            assert max(abs(spectrum["remainder"][k])
                       for k in ["minimum", "maximum"]) <= .25+2e-8
            if first is None:
                w = spectrum["response"]
                witnesses[limit] = (np.array(w["witness_real"])+
                                    1j*np.array(w["witness_imag"]))
            witness = witnesses[limit]
            q = old.value(sub["response"], witness)/old.value(sub["energy"], witness)
            spaces.append(dict(frequency_limit=limit, indices=ids,
                               spectrum=spectrum, first_witness_quotient=q))
        minima = [s["spectrum"]["response"]["minimum"] for s in spaces]
        assert all(b <= a+2e-8 for a, b in zip(minima, minima[1:]))
        if first is None:
            first = forms
        runs.append(dict(quadrature=setting, checks=checks, spaces=spaces,
                         full_energy_conditioning=condition,
                         energy_scaled_matrix_changes=changes,
                         matrices={name: transverse.matrix_record(M)
                                   for name, M in forms.items()},
                         seconds=time.monotonic()-start))
        print(json.dumps(dict(quadrature=setting,
                              dimensions=[len(s["indices"]) for s in spaces],
                              minimum_full_response_over_energy=minima,
                              maximum_matrix_change=max(changes.values(), default=0.))),
              flush=True)
    paths = [
        "scripts/nested_clock_response_probe.py",
        "scripts/verify_nested_clock_response.py",
        "scripts/independent_neutral_response_probe.py",
        "scripts/independent_neutral_moment_probe.py",
        "scripts/projected_initial_moment_probe.py",
        "scripts/projected_integrated_response_probe.py",
        "scripts/projected_kernel_matrix_probe.py",
        "scripts/projected_matter_cost_probe.py",
        "scripts/matter_energy_gram_probe.py",
        "scripts/displaced_signed_response_probe.py",
        "scripts/zero_charge_response_probe.py",
        "UnifiedTheory/Audit/KFCausalIndependentNeutralTestFamily.lean",
        "UnifiedTheory/Audit/KFCausalStructuredProjectedHamiltonian.lean",
        "UnifiedTheory/Audit/KFCausalProjectedClockResponse.lean",
    ]
    report = dict(
        kind="Nested signed response test with neutral and clock interference",
        packets=PACKETS, frequency_limits=LIMITS, h=.05, eps=1.,
        physical_time=0., couplings=dict(mass2=1., quartic=1., vacuum=1.),
        runs=runs, source_sha256={p: sha(root/p) for p in paths},
        formal_checkpoint=dict(path=PARENT, sha256=PARENT_SHA,
                               preserved_source_count=len(parent["source_sha256"])),
        limitations=[
            "Floating integration; no certified clock tails or quadrature enclosure.",
            "No new Lean theorem or uniform state/time/regulator bound.",
            "All complex modes retained; unresolved Gram modes rejected.",
            "The whole-clock forms retain all eight factors and charge-angle interference.",
            "Independent verification checks saved matrices, not an independent quadrature.",
            "The inherited kernel/direct-pairing implementations share numerical helpers.",
            "A negative fixed-time response does not prove a failing trajectory.",
            "No exclusion of negative spectral escape, necessary model revision or physical TOE.",
        ])
    assert sha(root/PARENT) == PARENT_SHA
    assert all(sha(root/p) == h for p, h in parent["source_sha256"].items())
    check_root_prefix(root, parent)
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+"\n")
    print(args.output, flush=True)


if __name__ == "__main__":
    main()
