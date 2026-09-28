import PrimeFactorOscillations.Proof.PrimeClusters.QuantitativeClosed
import PrimeGapsTheory.NumberTheory.Admissible

set_option autoImplicit false

/-! # WindowCount in the quantitative prime-cluster count -/

set_option maxRecDepth 4096

namespace PrimeGaps

theorem prime_tuple_count_le_window {k H : Nat} (h : Fin k -> Nat)
    (hinj : Function.Injective h) (hbound : forall i, h i <= H) (n : Nat) :
    (Finset.univ.filter (fun i : Fin k => Nat.Prime (n + h i))).card <=
      ((Finset.Icc n (n + H)).filter Nat.Prime).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun i => n + h i)
  next =>
    intro i hi
    have hp := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    exact And.intro (Finset.mem_Icc.mpr (And.intro
      (show n <= n + h i from Nat.le_add_right n (h i))
      (show n + h i <= n + H from Nat.add_le_add_left (hbound i) n))) hp
  next =>
    intro i _ j _ hij
    apply hinj
    change n + h i = n + h j at hij
    exact Nat.add_left_cancel hij

theorem eventually_many_prime_windows_600 :
    Filter.Eventually (fun N : Nat =>
      (N : Real) ^ ((1 : Real) / 3) <=
        (((Finset.Ioc N (2 * N)).filter (fun n =>
          2 <= ((Finset.Icc n (n + 600)).filter Nat.Prime).card)).card : Real))
      Filter.atTop := by
  classical
  let h : Fin 105 -> Nat := H105.orderEmbOfFin card_H105
  have himg : Finset.image h Finset.univ = H105 :=
    H105.image_orderEmbOfFin_univ card_H105
  have hmono : StrictMono h := (H105.orderEmbOfFin card_H105).strictMono
  have hadm : GPYSieveS1.IsAdmissible h :=
    And.intro hmono (by rw [himg]; exact admissible_H105)
  have hmax : H105.sup id = 600 := by
    set_option maxRecDepth 8192 in rfl
  have hbound : forall i, h i <= 600 := by
    intro i
    have hm : Membership.mem H105 (h i) := by
      rw [<- himg]
      exact Finset.mem_image_of_mem h (Finset.mem_univ i)
    have hb : h i <= H105.sup id := Finset.le_sup (f := id) hm
    exact hb.trans hmax.le
  apply (eventually_many_prime_cluster_shifts_105 h hadm).mono
  intro N hN
  apply hN.trans
  exact_mod_cast Finset.card_le_card (show
      (Finset.Ioc N (2 * N)).filter (fun n =>
        2 <= (Finset.univ.filter (fun i : Fin 105 => Nat.Prime (n + h i))).card)
      <= (Finset.Ioc N (2 * N)).filter (fun n =>
        2 <= ((Finset.Icc n (n + 600)).filter Nat.Prime).card) from by
    intro n hn
    have hm := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr (And.intro hm.1
      (hm.2.trans (prime_tuple_count_le_window h hmono.injective hbound n))))

end PrimeGaps
