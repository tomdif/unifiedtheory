# Causal Higgs numerical prototype

This directory preserves the March 2026 numerical prototype and its recorded
scaling experiments. It is supporting research, not the current roadmap for
completing the theory. [Current repository status](../STATUS.md).

The code explores scalar fields on a causal base with an internal fiber,
then computes candidate overlap/Yukawa matrices. The recorded two-dimensional
`S^1` prototype does not establish a physical four-dimensional `CP^2` limit,
Standard Model flavor dynamics, or a reduction of the physical parameter count.
The old manuscript and its outline have been removed.

## Implemented components

- `phase0/`: `CP^2` fiber geometry, causal-base and product operators, a scalar
  action, numerical solvers, and overlap observables.
- `phase1/`: the `S^1` prototype and scaling-study scripts, with recorded
  `scaling_results.json` and `scaling_results_full.json`.
- `tests/`: fiber-geometry and d'Alembertian checks.

The Python code requires NumPy and SciPy. No MPI/PETSc implementation or
large-scale four-dimensional result is claimed here. The repository-wide
audit checks syntax and saved JSON; reproducing the scaling experiments is
a separate numerical task.
