#!/usr/bin/env python3
"""Check complete nested response spectra independently of the producer.

Uses Cholesky scaling and direct generalized eigenvalues on saved matrices.
Does not certify the quadrature, physical evolution or an infinite-space bound.
"""
import hashlib
import json
from pathlib import Path
import numpy as np
from scipy.linalg import cholesky, eigh, solve_triangular


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def matrix(raw):
    return np.array(raw["real"])+1j*np.array(raw["imag"])


def scaling(E):
    W = solve_triangular(cholesky(E, lower=True).conj().T,
                         np.eye(len(E)), lower=False)
    assert np.linalg.norm(W.conj().T@E@W-np.eye(len(E)), 2) < 2e-8
    return W


def quotient(M, E, w):
    return float(np.vdot(w, M@w).real/np.vdot(w, E@w).real)


def main():
    root = Path(__file__).resolve().parents[1]
    path = root/"data/nested_clock_response_probe.json"
    report = json.loads(path.read_text())
    assert all(sha(root/p) == h for p, h in report["source_sha256"].items())
    checkpoint = report["formal_checkpoint"]
    assert checkpoint["path"] == "data/quantum_full_time_spectrum_audit.json"
    assert checkpoint["sha256"] == "6931e5e3ee971108a12a4bcfeb44100bce3ae19e74a343d1cfaf858f410c8470"
    assert sha(root/checkpoint["path"]) == checkpoint["sha256"]
    parent = json.loads((root/checkpoint["path"]).read_text())
    assert len(parent["source_sha256"]) == checkpoint["preserved_source_count"] == 2022
    assert all(sha(root/p) == h for p, h in parent["source_sha256"].items())
    lines = (root/"UnifiedTheory.lean").read_text().splitlines(keepends=True)
    assert hashlib.sha256("".join(lines[:7890]).encode()).hexdigest() == parent["root_check"]["source_sha256"]
    assert all(line.startswith("import ") and line.endswith("\n") for line in lines[7890:])
    packets = [[10., B, -.4, 1., float(p)]
               for B in [7., 8., 9.] for p in range(-32, 33, 2)]
    limits = [0, 4, 12, 24, 32]
    assert report["packets"] == packets and report["frequency_limits"] == limits
    assert report["h"] == .05 and report["eps"] == 1. and report["physical_time"] == 0.
    assert report["couplings"] == dict(mass2=1., quartic=1., vacuum=1.)
    assert [r["quadrature"] for r in report["runs"]] == [
        dict(nt=64, nd=512, left=-10., right=4., panels=96, order=14),
        dict(nt=96, nd=768, left=-12., right=4.5, panels=144, order=16)]
    first, witnesses, records = None, {}, []
    max_spectral_error = 0.
    direct_gaps = []
    for run in report["runs"]:
        forms = {n: matrix(m) for n, m in run["matrices"].items()}
        assert set(forms) == {"energy", "ordered", "remainder", "norm",
                              "ordered_direct", "remainder_direct", "response"}
        assert all(M.shape == (99, 99) and np.isfinite(M).all() for M in forms.values())
        assert all(np.linalg.norm(M-M.conj().T) <= 2e-10*max(1., np.linalg.norm(M))
                   for M in forms.values())
        E = forms["energy"]
        W = scaling(E)
        assert np.linalg.norm(W.conj().T@
                              (forms["response"]-forms["ordered"]-forms["remainder"])@W, 2) < 2e-10
        condition = run["full_energy_conditioning"]
        assert condition["rank_truncated"] is False and condition["dimension"] == 99
        assert condition["whitening_residual"] < 2e-8
        assert max(run["checks"]["integration_by_parts_errors"].values()) < 2e-8
        assert max(run["checks"]["boundary_over_energy"].values()) < 2e-8
        assert run["checks"]["projected_gram_oracle_error"] < 5e-10
        # The reported endpoint matrices are negligible on these whole-clock
        # grids. Test the direct/reduced discrepancy in the full energy metric,
        # so a large Euclidean mode cannot hide an error in a smaller one.
        gaps = {n: float(np.linalg.norm(W.conj().T@
                                       (forms[n+"_direct"]-forms[n])@W, 2))
                for n in ["ordered", "remainder"]}
        assert max(gaps.values()) < 2e-8, gaps
        direct_gaps.append(gaps)
        changes = {} if first is None else {
            n: float(np.linalg.norm(W.conj().T@(M-first[n])@W, 2)/
                     max(1., np.linalg.norm(W.conj().T@M@W, 2)))
            for n, M in forms.items()}
        assert changes.keys() == run["energy_scaled_matrix_changes"].keys()
        assert not changes or max(changes.values()) < 2e-8
        assert all(abs(v-run["energy_scaled_matrix_changes"][n]) < 2e-9
                   for n, v in changes.items())
        minima, prior_ids = [], set()
        assert len(run["spaces"]) == len(limits)
        for limit, saved in zip(limits, run["spaces"]):
            ids = [i for i, p in enumerate(packets) if abs(p[4]) <= limit]
            assert saved["frequency_limit"] == limit and saved["indices"] == ids
            assert prior_ids <= set(ids)
            prior_ids = set(ids)
            sub = {n: M[np.ix_(ids, ids)] for n, M in forms.items()}
            Es = sub["energy"]
            scaling(Es)
            condition = saved["spectrum"]["conditioning"]
            assert condition["rank_truncated"] is False
            assert condition["dimension"] == len(ids) and condition["whitening_residual"] < 2e-8
            for name in ["ordered", "response", "remainder", "norm"]:
                values = eigh(sub[name], Es, eigvals_only=True)
                spec = saved["spectrum"][name]
                error = max(abs(values[0]-spec["minimum"]), abs(values[-1]-spec["maximum"]))
                assert error < 2e-8
                max_spectral_error = max(max_spectral_error, float(error))
                w = np.array(spec["witness_real"])+1j*np.array(spec["witness_imag"])
                assert abs(np.vdot(w, Es@w)-1) < 2e-8
                assert abs(quotient(sub[name], Es, w)-values[0]) < 2e-8
                residual = np.linalg.norm(sub[name]@w-values[0]*(Es@w))/max(
                    1., np.linalg.norm(sub[name]@w), abs(values[0])*np.linalg.norm(Es@w))
                assert residual < 2e-8
                diagonal = float(np.min(sub[name].diagonal().real/Es.diagonal().real))
                assert abs(diagonal-spec["diagonal_minimum"]) < 2e-8
                if name == "norm":
                    assert values[0] >= -2e-10
                if name == "remainder":
                    assert max(abs(values)) <= .25+2e-8
                if name == "response":
                    minima.append(float(values[0]))
                    if first is None:
                        witnesses[limit] = w
            q = quotient(sub["response"], Es, witnesses[limit])
            assert abs(q-saved["first_witness_quotient"]) < 2e-8
            records.append(dict(quadrature=run["quadrature"], frequency_limit=limit,
                                dimension=len(ids), minimum_response=minima[-1],
                                first_witness_quotient=q))
        assert all(b <= a+2e-8 for a, b in zip(minima, minima[1:]))
        if first is None:
            first = forms
    target = root/"data/nested_clock_response_validation.json"
    result = dict(probe_report_sha256=sha(path), verifier_sha256=sha(Path(__file__)),
                  checks=records, maximum_spectral_error=max_spectral_error,
                  energy_scaled_direct_reduced_gaps=direct_gaps,
                  scope="Independent matrix spectra, witnesses, nesting, refinement and provenance. "
                        "No independent quadrature, certified error, uniform response bound, "
                        "evolution counterexample or new Lean theorem.")
    target.write_text(json.dumps(result, indent=2, allow_nan=False)+"\n")
    print("Independent verification passed: ten complete nested spaces, up to 99 complex modes; "
          "all 2022 formal checkpoint hashes and root preserved.")
    print(target)


if __name__ == "__main__":
    main()
