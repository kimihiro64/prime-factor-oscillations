"""New metaplectic arithmetic-model targets; no automorphic identification is implied."""

from scripts.adaptive_multiplicity_proof_targets import ADAPTIVE_MULTIPLICITY_THEOREMS
from scripts.carrier_stability_proof_targets import CARRIER_STABILITY_THEOREMS
from scripts.dirichlet_scalar_orbit_proof_targets import DIRICHLET_SCALAR_ORBIT_THEOREMS
from scripts.dyadic_carrier_proof_targets import DYADIC_CARRIER_THEOREMS
from scripts.exact_residue_spacing_proof_targets import EXACT_RESIDUE_SPACING_THEOREMS
from scripts.finite_real_packet_proof_targets import FINITE_REAL_PACKET_THEOREMS
from scripts.global_excess_proof_targets import GLOBAL_EXCESS_THEOREMS
from scripts.localized_multiplicity_proof_targets import LOCALIZED_MULTIPLICITY_THEOREMS
from scripts.metaplectic_base_proof_targets import METAPLECTIC_BASE_THEOREMS
from scripts.minimal_carrier_proof_targets import MINIMAL_CARRIER_THEOREMS
from scripts.multiplicity_carrier_proof_targets import MULTIPLICITY_CARRIER_THEOREMS
from scripts.multiplicity_lattice_proof_targets import MULTIPLICITY_LATTICE_THEOREMS
from scripts.multiplicity_support_proof_targets import MULTIPLICITY_SUPPORT_THEOREMS
from scripts.near_identity_panel_proof_targets import NEAR_IDENTITY_PANEL_THEOREMS
from scripts.optimal_residue_degree_proof_targets import OPTIMAL_RESIDUE_DEGREE_THEOREMS
from scripts.phase_multiplicity_proof_targets import PHASE_MULTIPLICITY_THEOREMS
from scripts.quadratic_scalar_chain_proof_targets import QUADRATIC_SCALAR_CHAIN_THEOREMS
from scripts.rational_single_real_proof_targets import RATIONAL_SINGLE_REAL_THEOREMS
from scripts.residue_panel_proof_targets import RESIDUE_PANEL_THEOREMS
from scripts.scalar_cubic_orbit_proof_targets import SCALAR_CUBIC_ORBIT_THEOREMS
from scripts.scalar_erasure_proof_targets import SCALAR_ERASURE_COST_THEOREMS
from scripts.simple_carrier_sharpness_proof_targets import SIMPLE_CARRIER_SHARPNESS_THEOREMS
from scripts.single_real_zeta_proof_targets import SINGLE_REAL_ZETA_THEOREMS
from scripts.strip_carrier_proof_targets import STRIP_CARRIER_THEOREMS
from scripts.two_power_degree_proof_targets import TWO_POWER_DEGREE_THEOREMS
from scripts.two_tail_proof_targets import TWO_TAIL_THEOREMS

METAPLECTIC_THEOREMS: tuple[str, ...] = tuple(
    sorted(
        METAPLECTIC_BASE_THEOREMS
        + STRIP_CARRIER_THEOREMS
        + DYADIC_CARRIER_THEOREMS
        + MULTIPLICITY_CARRIER_THEOREMS
        + SIMPLE_CARRIER_SHARPNESS_THEOREMS
        + MULTIPLICITY_SUPPORT_THEOREMS
        + CARRIER_STABILITY_THEOREMS
        + TWO_TAIL_THEOREMS
        + MINIMAL_CARRIER_THEOREMS
        + GLOBAL_EXCESS_THEOREMS
        + MULTIPLICITY_LATTICE_THEOREMS
        + ADAPTIVE_MULTIPLICITY_THEOREMS
        + EXACT_RESIDUE_SPACING_THEOREMS
        + OPTIMAL_RESIDUE_DEGREE_THEOREMS
        + RESIDUE_PANEL_THEOREMS
        + TWO_POWER_DEGREE_THEOREMS
        + SCALAR_CUBIC_ORBIT_THEOREMS
        + DIRICHLET_SCALAR_ORBIT_THEOREMS
        + QUADRATIC_SCALAR_CHAIN_THEOREMS
        + RATIONAL_SINGLE_REAL_THEOREMS
        + FINITE_REAL_PACKET_THEOREMS
        + NEAR_IDENTITY_PANEL_THEOREMS
        + PHASE_MULTIPLICITY_THEOREMS
        + LOCALIZED_MULTIPLICITY_THEOREMS
        + SCALAR_ERASURE_COST_THEOREMS
        + SINGLE_REAL_ZETA_THEOREMS
    )
)
