#!/usr/bin/env python3
"""Numerical correspondence for the globally constructed finite dynamics.

Compare the linear equation to the bounded auxiliary equation used in the
Lean existence proof, in both time directions and on overlapping intervals.
Numerical solves do not establish existence for all times or capacities.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy
import scipy.linalg as la
from scipy.integrate import solve_ivp

from constraint_reduced_spin_model import ConstraintReducedSpinModel, Parameters


def check_flow(capacity, correction, direction):
    model = ConstraintReducedSpinModel(Parameters(
        R=capacity, flavors=6, correction=correction, hbar=0.2,
        vacuum=0.03, functional_order=2))
    d = model.dim
    identity = np.eye(d, dtype=complex)
    projector = np.diag((model.charge == 0).astype(float))
    end = direction * 0.4
    grid = np.linspace(0, end, 5)

    def integrate(auxiliary, stop, times):
        def rhs(t, flat):
            U = flat.reshape(d, d)
            if auxiliary:
                U = 2 / (1 + la.norm(U, 2)) * U
            return (-1j / model.params.hbar * model.matrix(t) @ U).ravel()
        result = solve_ivp(rhs, (0, stop), identity.ravel(), method="DOP853",
                           t_eval=times, rtol=2e-13, atol=2e-15, max_step=0.005)
        assert result.success, result.message
        return result.y.T.reshape(-1, d, d)

    linear = integrate(False, end, grid)
    auxiliary = integrate(True, end, grid)
    # Independent solves to different interval ends should agree at the overlap.
    short = integrate(True, end / 2, grid[:3])
    metrics = {
        "auxiliary_linear_error": max(la.norm(a-b) for a, b in zip(auxiliary, linear)),
        "overlap_error": max(la.norm(a-b) for a, b in zip(auxiliary[:3], short)),
        "unitarity_error": max(la.norm(U.conj().T @ U-identity) for U in auxiliary),
        "operator_norm_error": max(abs(la.norm(U, 2)-1) for U in auxiliary),
        "constraint_error": max(la.norm(model.constraint @ U @ projector) for U in auxiliary),
        "projector_error": max(la.norm(U.conj().T @ projector @ U-projector) for U in auxiliary),
    }
    assert max(metrics.values()) < 2e-9, (capacity, correction, direction, metrics)
    return dict(capacity=capacity, correction=correction, dimension=d,
                time_interval=[0, end], **{k: float(v) for k, v in metrics.items()})


def main():
    cases = [check_flow(R, profile, direction)
             for R in [1, 2] for profile in ["bare", "second_order", "exact"]
             for direction in [-1, 1]]
    root = Path(__file__).resolve().parents[1]
    earlier = json.loads((root / "data/positive_clock_continuous_audit.json").read_text())
    sources = list(earlier["source_sha256"])
    sources += ["scripts/global_spin_dynamics_audit.py"]
    sources += ["UnifiedTheory/Audit/" + name + ".lean" for name in [
        "KFCausalRadialCutoff", "KFCausalIntervalPropagator",
        "KFCausalGlobalPropagator", "KFCausalGlobalSpinDynamics"]]
    hashes = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    # Preserve the earlier operator-correspondence evidence's provenance.
    assert all(hashes[p] == h for p, h in earlier["source_sha256"].items())
    report = dict(
        cases=cases, source_sha256=hashes,
        solver=dict(method="DOP853", rtol=2e-13, atol=2e-15, max_step=0.005),
        numerical_environment=dict(numpy=np.__version__, scipy=scipy.__version__),
        lean_toolchain=(root/"lean-toolchain").read_text().strip(),
        scope=("Numerical correspondence of the original finite linear equation and the bounded "
               "auxiliary equation used to construct the Lean global propagator. Lean separately "
               "proves existence, uniqueness, unitarity and physical-sector constraint preservation "
               "for every finite capacity and every real time. This does not establish a continuum "
               "limit, microscopic sector selection, vanishing finite-clock error or a TOE."))
    target = root/"data/global_spin_dynamics_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{target}: {len(cases)} forward/backward flow cases passed.")
    print({key: max(case[key] for case in cases) for key in cases[0] if key.endswith("error")})


if __name__ == "__main__":
    main()
