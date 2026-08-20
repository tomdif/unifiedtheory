#!/usr/bin/env python3
"""One-birth proxy channels for the physical Hauptvermutung certificate errors.

The Lean bridge `KFCausalCSpecHauptvermutungPhysicalBridge.lean` names three
physical-growth certificate errors:

  * countWindow
  * curvatureBias
  * pairConsistency

This module builds finite one-birth estimators with those names.  They are not
the certificate itself; they are local proxy observables over candidate
precursor downsets `D`, intended for source-design and null-cone scans.
"""

import math

import numpy as np

from horizon_hauptvermutung_channels import d_from_f, interval_profile_for_birth


DEFAULT_CERT_CHANNELS = (
    "cert_countWindow,cert_curvatureBias,cert_pairConsistency,"
    "cert_distortionBound,cert_scaledDistortionBound,"
    "cert_target4Distortion,cert_target2Distortion,"
    "-gap,interior_bdg,size"
)


def _mean_abs_relative(x):
    x = np.array(x, dtype=float)
    x = x[np.isfinite(x)]
    if len(x) == 0:
        return 0.0
    mu = float(np.mean(x))
    if abs(mu) <= 1e-14:
        return 0.0
    return float(np.mean(np.abs(x / mu - 1.0)))


def _mean_pair_abs(x):
    x = np.array(x, dtype=float)
    x = x[np.isfinite(x)]
    if len(x) < 2:
        return 0.0
    total = 0.0
    count = 0
    for i in range(len(x)):
        for j in range(i + 1, len(x)):
            total += abs(float(x[i] - x[j]))
            count += 1
    return total / count if count else 0.0


def _scale_drift(log_sizes, dims):
    log_sizes = np.array(log_sizes, dtype=float)
    dims = np.array(dims, dtype=float)
    mask = np.isfinite(log_sizes) & np.isfinite(dims)
    log_sizes = log_sizes[mask]
    dims = dims[mask]
    if len(dims) < 2:
        return 0.0
    span = float(np.max(log_sizes) - np.min(log_sizes))
    if span <= 1e-14:
        return float(np.std(dims))
    cov = float(np.mean((log_sizes - np.mean(log_sizes)) * (dims - np.mean(dims))))
    var = float(np.mean((log_sizes - np.mean(log_sizes)) ** 2))
    slope = cov / var if var > 1e-14 else 0.0
    residual = dims - (np.mean(dims) + slope * (log_sizes - np.mean(log_sizes)))
    return abs(slope) + float(np.std(residual))


def _target_distortion(dims, target):
    dims = np.array(dims, dtype=float)
    dims = dims[np.isfinite(dims)]
    if len(dims) == 0:
        return 0.0
    return float(np.mean(np.abs(dims - target)))


def _certificate_errors_for_birth(D, below, above):
    dims, rel_fracs, log_sizes = interval_profile_for_birth(D, below, above)
    if not dims:
        return {
            "countWindow": 0.0,
            "curvatureBias": 0.0,
            "pairConsistency": 0.0,
            "scale": 0.0,
            "target4": 0.0,
            "target2": 0.0,
        }

    counts = [math.expm1(x) for x in log_sizes]
    count_window = _mean_abs_relative(counts)
    curvature_bias = _scale_drift(log_sizes, dims)
    pair_consistency = _mean_pair_abs(dims)
    scale = max(log_sizes) if log_sizes else 0.0

    return {
        "countWindow": count_window,
        "curvatureBias": curvature_bias,
        "pairConsistency": pair_consistency,
        "scale": scale,
        "target4": _target_distortion(dims, 4.0),
        "target2": _target_distortion(dims, 2.0),
    }


def augment_certificate_observables(dlist, below, above, obs):
    cert_count = np.zeros(len(dlist), dtype=float)
    cert_curv = np.zeros(len(dlist), dtype=float)
    cert_pair = np.zeros(len(dlist), dtype=float)
    cert_bound = np.zeros(len(dlist), dtype=float)
    cert_scaled = np.zeros(len(dlist), dtype=float)
    cert_target4 = np.zeros(len(dlist), dtype=float)
    cert_target2 = np.zeros(len(dlist), dtype=float)

    for idx, D0 in enumerate(dlist):
        e = _certificate_errors_for_birth(int(D0), below, above)
        cw = e["countWindow"]
        cb = e["curvatureBias"]
        pc = e["pairConsistency"]
        sc = e["scale"]
        cert_count[idx] = cw
        cert_curv[idx] = cb
        cert_pair[idx] = pc
        cert_bound[idx] = cw + cb + cw * cb + pc / 2.0
        cert_scaled[idx] = (cw + cb + cw * cb) * sc + pc / 2.0
        cert_target4[idx] = e["target4"] + cert_bound[idx]
        cert_target2[idx] = e["target2"] + cert_bound[idx]

    obs.update({
        "cert_countWindow": cert_count,
        "cert_curvatureBias": cert_curv,
        "cert_pairConsistency": cert_pair,
        "cert_distortionBound": cert_bound,
        "cert_scaledDistortionBound": cert_scaled,
        "cert_target4Distortion": cert_target4,
        "cert_target2Distortion": cert_target2,
    })
    return obs
