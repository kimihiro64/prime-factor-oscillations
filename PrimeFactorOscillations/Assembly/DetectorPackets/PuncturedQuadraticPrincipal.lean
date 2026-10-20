/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Detector.TupleScaling
import PrimeFactorOscillations.Assembly.DetectorPackets.FullQuotientQuadraticMean

/-!
# PuncturedQuadraticPrincipal

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Punctured quadratic phase: exact signal and physical normalization

The actual punctured marked series has P = -D and V = 0. Here the complete
Euler-coordinate multiplier, with numerator and reciprocal retained, is
normalized exactly. At the principal frequency its value is independent
of the Mellin variable and is nonzero. The same normalization requires
simultaneous changes of the physical X and Z scales, recorded explicitly.

This is a local pole-factor and scale identity, not the assembled Mellin
residue theorem or an estimate for the weighted global quotient packet.
-/

set_option maxHeartbeats 800000

noncomputable section
namespace OAI.SevenEighths.PuncturedQuadraticPrincipal

open ProbeLocal ProbeEuler SexticToQuadraticLocal
open FullQuotientQuadraticMean ProbePhysical

theorem punctured_full (W D B q c : Complex)
    (hW : Not (1-W=0)) (hD : Not (1-D=0))
    (hBD : B*D=c) (hcW : c*W=q) :
    (1-D)*enhancedReplacement 0 W D (-D) B q c/(1-W) =
      -c*D^2*(1-W)^2 := by
  have h := full_euler_identity 0 W D (-D) B q c (by norm_num) hW hD hBD hcW
  simpa only [retainedDefect, neg_add_cancel, mul_zero, add_zero, zero_mul,
    sub_zero, one_mul, div_one, zero_div] using h

theorem normalized_full (Q : Real) (eta v x w : Complex)
    (hQ : 0<Q) (heta : norm eta=1) (hv : norm v=1)
    (hW : Not (1-coordW Q v w=0)) (hD : Not (1-coordD Q eta v x=0)) :
    (Q:Complex)^(2*x)*
      ((1-coordD Q eta v x)*
        enhancedReplacement 0 (coordW Q v w) (coordD Q eta v x)
          (-coordD Q eta v x) (star eta*(Q:Complex)^x)
          ((Q:Complex)^(-w)) (star v)/(1-coordW Q v w)) =
      -eta^2*(star v)^3*(1-coordW Q v w)^2 := by
  have hi := selected_phase_identities Q eta v x w hQ heta hv
  rw [punctured_full _ _ _ _ _ hW hD hi.1 hi.2]
  have hQ0 : Not ((Q:Complex)=0) := by exact_mod_cast hQ.ne'
  have hp : (Q:Complex)^(2*x)*(Q:Complex)^(-2*x)=1 := by
    rw [<-Complex.cpow_add _ _ hQ0]
    simp
  have hc := cubic_phase_coefficient Q eta v x hQ
  calc
    _ = -((Q:Complex)^(2*x)*(star v*(coordD Q eta v x)^2))*
        (1-coordW Q v w)^2 := by ring
    _ = -((Q:Complex)^(2*x)*(eta^2*(star v)^3*(Q:Complex)^(-2*x)))*
        (1-coordW Q v w)^2 := by rw [hc]
    _ = -(eta^2*(star v)^3*((Q:Complex)^(2*x)*(Q:Complex)^(-2*x)))*
        (1-coordW Q v w)^2 := by ring
    _ = _ := by rw [hp]; ring

theorem principal_exact (Q : Real) (eta x : Complex)
    (hQ : 0<Q) (heta : norm eta=1) (heta2 : eta^2=1)
    (hW : Not (1-coordW Q 1 1=0)) (hD : Not (1-coordD Q eta 1 x=0)) :
    (Q:Complex)^(2*x)*
      ((1-coordD Q eta 1 x)*
        enhancedReplacement 0 (coordW Q 1 1) (coordD Q eta 1 x)
          (-coordD Q eta 1 x) (star eta*(Q:Complex)^x)
          ((Q:Complex)^(-(1:Complex))) 1/(1-coordW Q 1 1)) =
      -(1-(Q:Complex)^(-(1:Complex)))^2 := by
  simpa only [star_one, one_pow, mul_one, heta2, coordW, one_mul, neg_mul,
    one_pow] using
    normalized_full Q eta 1 x 1 hQ heta (by simp) hW hD

theorem principal_factor_ne_zero (Q : Real) (hQ : 1<Q) :
    Not (-(1-(Q:Complex)^(-(1:Complex)))^2=0) := by
  have hQ0 : Not ((Q:Complex)=0) := by exact_mod_cast (lt_trans (by norm_num) hQ).ne'
  have hQ1 : Not ((Q:Complex)=1) := by exact_mod_cast (ne_of_gt hQ)
  have hd : Not (1-(Q:Complex)^(-(1:Complex))=0) := by
    intro h
    simp only [Complex.cpow_neg_one] at h
    field_simp [hQ0] at h
    exact hQ1 (by linear_combination h)
  exact neg_ne_zero.mpr (pow_ne_zero 2 hd)

theorem source_weight_joint_scale (W0 W1 : SchwartzMap Real Complex)
    (X Y Z Q : Real) (hX : 0<X) (hZ : 0<Z) (hQ : 0<Q)
    (x w z : Complex) :
    sourceMellinWeight W0 W1 (X*Q) Y (Z*Q) x w z =
      (Q:Complex)^(x-1/2)*sourceMellinWeight W0 W1 X Y Z x w z := by
  have hQ0 : Not ((Q:Complex)=0) := by exact_mod_cast hQ.ne'
  unfold sourceMellinWeight
  rw [Complex.ofReal_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hX.le hQ.le,
    Complex.mul_cpow_ofReal_nonneg hZ.le hQ.le]
  have hp : (Q:Complex)^(1/2-z)*(Q:Complex)^(x+z-1) =
      (Q:Complex)^(x-1/2) := by
    rw [<-Complex.cpow_add _ _ hQ0]
    congr 1
    ring
  calc
    _ = ((Q:Complex)^(1/2-z)*(Q:Complex)^(x+z-1))*
        ((X:Complex)^(1/2-z)*(Z:Complex)^(x+z-1)*(Y:Complex)^(w-1)*
          Complex.exp ((x+z-1)^2)*
          mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*mellin W1 w) := by ring
    _ = _ := by rw [hp]

theorem normalization_scale_cost (W0 W1 : SchwartzMap Real Complex)
    (X Y Z Q : Real) (hX : 0<X) (hZ : 0<Z) (hQ : 0<Q)
    (x w z : Complex) :
    (Q:Complex)*sourceMellinWeight W0 W1 (X*Q^2) Y (Z*Q^2) x w z =
      (Q:Complex)^(2*x)*sourceMellinWeight W0 W1 X Y Z x w z := by
  have hQ0 : Not ((Q:Complex)=0) := by exact_mod_cast hQ.ne'
  rw [show X*Q^2=(X*Q)*Q by ring, show Z*Q^2=(Z*Q)*Q by ring,
    source_weight_joint_scale W0 W1 (X*Q) Y (Z*Q) Q (mul_pos hX hQ) (mul_pos hZ hQ) hQ,
    source_weight_joint_scale W0 W1 X Y Z Q hX hZ hQ]
  have hp : (Q:Complex)*((Q:Complex)^(x-1/2)*(Q:Complex)^(x-1/2)) =
      (Q:Complex)^(2*x) := by
    conv_lhs => lhs; rw [<-Complex.cpow_one (Q:Complex)]
    rw [<-Complex.cpow_add _ _ hQ0, <-Complex.cpow_add _ _ hQ0]
    congr 1
    ring
  calc
    _ = ((Q:Complex)*((Q:Complex)^(x-1/2)*(Q:Complex)^(x-1/2)))*
        sourceMellinWeight W0 W1 X Y Z x w z := by ring
    _ = _ := by rw [hp]

end OAI.SevenEighths.PuncturedQuadraticPrincipal

