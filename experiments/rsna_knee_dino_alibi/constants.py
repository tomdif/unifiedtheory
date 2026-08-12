"""Competition constants shared by extraction, training, and inference."""

from __future__ import annotations

TARGETS = [
    "ACL",
    "MCL",
    "Medial Meniscus",
    "Lateral Meniscus",
    "Medial OA",
    "Lateral OA",
    "PF OA",
    "Effusion",
    "Synovitis",
    "Baker's",
    "Contusion",
    "Fracture",
]

# Fixed clinical routing priors.  These are deliberately declared in one
# place rather than fitted on the 58 expert studies.  A value of one means
# that a plane is considered directly informative enough to receive the
# auxiliary branch loss for the target.  The final cross-plane prediction is
# never masked: secondary planes can still contribute through learned fusion.
TARGET_PLANE_SUPPORT = {
    "ACL": ("sagittal", "coronal"),
    "MCL": ("coronal", "axial"),
    "Medial Meniscus": ("sagittal", "coronal"),
    "Lateral Meniscus": ("sagittal", "coronal"),
    "Medial OA": ("sagittal", "coronal", "axial"),
    "Lateral OA": ("sagittal", "coronal", "axial"),
    "PF OA": ("sagittal", "axial"),
    "Effusion": ("sagittal", "axial"),
    "Synovitis": ("sagittal", "axial"),
    "Baker's": ("sagittal", "axial"),
    "Contusion": ("sagittal", "coronal", "axial"),
    "Fracture": ("sagittal", "coronal", "axial"),
}

# Targets share an image encoder, but their final residual evidence paths are
# grouped by tissue/appearance to avoid forcing fluid, ligament, meniscal and
# osseous findings through the same small head.  These indices are a modeling
# prior, not an OOF-fitted router.
TARGET_FAMILIES = {
    "ligament": ("ACL", "MCL"),
    "meniscus": ("Medial Meniscus", "Lateral Meniscus"),
    "degenerative": ("Medial OA", "Lateral OA", "PF OA"),
    "fluid_synovial": ("Effusion", "Synovitis", "Baker's"),
    "bone_trauma": ("Contusion", "Fracture"),
}

PLANE_TO_ID = {
    "unknown": 0,
    "sagittal": 1,
    "coronal": 2,
    "axial": 3,
}

# 0 is unknown, 1 is false, 2 is true.  This distinguishes absent metadata
# from a measured negative value.
TRISTATE_UNKNOWN = 0
TRISTATE_FALSE = 1
TRISTATE_TRUE = 2

CACHE_SCHEMA_VERSION = 1
