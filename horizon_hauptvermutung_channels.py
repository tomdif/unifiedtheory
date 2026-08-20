#!/usr/bin/env python3
"""Hauptvermutung-oriented one-birth defect channels.

The earlier null-cone scans used shell-count proxies such as `h0`, `h1`, and
`h2`.  This module adds channels closer to the physical-growth certificate:

  * local interval dimension error;
  * interval relation-fraction bias against 2D/4D calibrations;
  * interval-profile spread;
  * local count-window/scale irregularity.

Each channel is a vector over possible next-birth precursor downsets `D`.
The functions are intentionally finite and local: they only inspect intervals
ending at the proposed new birth.
"""

import math

import numpy as np

from horizon_entropy_probe import bitcount


DEFAULT_HV_CHANNELS = (
    "hv_dim4_err,hv_dim2_err,hv_rel4_abs,hv_rel2_abs,"
    "hv_dim_spread,hv_logk_spread,hv_interval_mass,hv_big_interval_count,"
    "-gap,interior_bdg,size"
)

MM_D = np.array([1.5, 2, 3, 4, 5, 6, 8, 10], float)
MM_F = np.array([0.75, 0.5000, 0.2296, 0.0994, 0.0417, 0.0170, 0.00287, 0.000496])
_ORD = np.argsort(-np.log(MM_F))
_XP = (-np.log(MM_F))[_ORD]
_FP = MM_D[_ORD]

F2 = 0.5000
F4 = 0.0994


def d_from_f(f):
    if f is None or f <= 0 or not math.isfinite(f):
        return float("nan")
    return float(np.interp(-math.log(f), _XP, _FP))


def interval_profile_for_birth(D, below, above):
    dims = []
    rel_fracs = []
    log_sizes = []
    m = int(D)
    while m:
        y = (m & -m).bit_length() - 1
        inter = int(above[y]) & int(D)
        k = bitcount(inter)
        if k >= 4:
            elems = []
            mm = inter
            while mm:
                e = (mm & -mm).bit_length() - 1
                elems.append(e)
                mm &= mm - 1
            nrel = sum(bitcount(int(below[e]) & inter) for e in elems)
            f = nrel / (k * (k - 1) / 2)
            d = d_from_f(f)
            if math.isfinite(d):
                dims.append(d)
                rel_fracs.append(f)
                log_sizes.append(math.log1p(k))
        m &= m - 1
    return dims, rel_fracs, log_sizes


def augment_hauptvermutung_observables(dlist, below, above, obs):
    hv_dim4_err = np.zeros(len(dlist), dtype=float)
    hv_dim2_err = np.zeros(len(dlist), dtype=float)
    hv_rel4_abs = np.zeros(len(dlist), dtype=float)
    hv_rel2_abs = np.zeros(len(dlist), dtype=float)
    hv_dim_spread = np.zeros(len(dlist), dtype=float)
    hv_logk_spread = np.zeros(len(dlist), dtype=float)
    hv_interval_mass = np.zeros(len(dlist), dtype=float)
    hv_big_interval_count = np.zeros(len(dlist), dtype=float)

    for idx, D0 in enumerate(dlist):
        dims, rel_fracs, log_sizes = interval_profile_for_birth(int(D0), below, above)
        if not dims:
            continue
        d = np.array(dims, dtype=float)
        f = np.array(rel_fracs, dtype=float)
        lk = np.array(log_sizes, dtype=float)
        hv_dim4_err[idx] = float(np.mean((d - 4.0) ** 2))
        hv_dim2_err[idx] = float(np.mean((d - 2.0) ** 2))
        hv_rel4_abs[idx] = float(np.mean(np.abs(f - F4)))
        hv_rel2_abs[idx] = float(np.mean(np.abs(f - F2)))
        hv_dim_spread[idx] = float(np.var(d))
        hv_logk_spread[idx] = float(np.var(lk))
        hv_interval_mass[idx] = float(len(dims))
        hv_big_interval_count[idx] = float(sum(1 for x in log_sizes if x >= math.log1p(8)))

    obs.update({
        "hv_dim4_err": hv_dim4_err,
        "hv_dim2_err": hv_dim2_err,
        "hv_rel4_abs": hv_rel4_abs,
        "hv_rel2_abs": hv_rel2_abs,
        "hv_dim_spread": hv_dim_spread,
        "hv_logk_spread": hv_logk_spread,
        "hv_interval_mass": hv_interval_mass,
        "hv_big_interval_count": hv_big_interval_count,
    })
    return obs
