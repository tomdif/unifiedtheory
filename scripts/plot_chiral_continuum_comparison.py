#!/usr/bin/env python3
"""Plot recorded flat and curved comparisons without extrapolating a limit."""
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]


def main():
    flat = json.loads((ROOT/'data/chiral_continuum_comparison.json').read_text())
    curved = json.loads((ROOT/'data/chiral_curved_response_refinement.json').read_text())
    fig, axes = plt.subplots(1, 2, figsize=(11, 4.5), layout='constrained')
    rows = flat['flat_holonomy']['rows']
    for h in sorted({r['h'] for r in rows}):
        selected = sorted((r for r in rows if r['h'] == h), key=lambda r:r['n'])
        axes[0].loglog([r['n'] for r in selected], [r['log_error'] for r in selected],
                       'o-', markersize=4, label=f'h = {h}')
    axes[0].set(title='Flat holonomy log-weight error', xlabel='Lattice side N',
                ylabel='Absolute error against continuum')
    axes[0].legend(frameon=False)
    rows = sorted(curved['overlap'], key=lambda r:r['n'])
    axes[1].plot([r['n'] for r in rows], [r['current_t4_imag']*1e6 for r in rows],
                 'o-', color='#176A9A', label='Overlap dynamical current')
    reference = max(curved['continuum'], key=lambda r:r['cutoff'])
    axes[1].axhline(reference['current_t4_imag']*1e6, color='#B34C27', linestyle='--',
                   label=f"Continuum, cutoff {reference['cutoff']}")
    axes[1].set(title='Curved fifth-order phase response', xlabel='Lattice side N',
                ylabel='Imaginary current coefficient β (×10⁻⁶)')
    axes[1].set_xticks([r['n'] for r in rows])
    axes[1].legend(frameon=False)
    for ax in axes:
        ax.grid(alpha=.2)
        ax.spines[['right', 'top']].set_visible(False)
    fig.suptitle('Overlap and continuum Weyl comparisons\n'
                 'Curved response excludes the completed measure phase', fontsize=12)
    output = ROOT/'results'
    output.mkdir(exist_ok=True)
    for suffix in ['png', 'svg']:
        fig.savefig(output/f'chiral_continuum_comparison.{suffix}', dpi=180)
    plt.close(fig)


if __name__ == '__main__':
    main()
