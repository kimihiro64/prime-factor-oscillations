import Mathlib.Data.Finset.Sort
import PrimeFactorOscillations.Helpers.PrimeWindowPairs
import PrimeFactorOscillations.Mathlib.Data.Nat.Prime.FactorialCellCount
import PrimeFactorOscillations.Mathlib.Data.Nat.Prime.FactorialCellSelection

/-! # Finite prime-window counts and separated gap witnesses -/

namespace PrimeFactorUnimodality

/-- Finite prime-window counts force many disjoint long-gap/short-gap pairs. -/
theorem prime_windows_separated_gap_pairs (S : Finset Nat) (hS : S.Nonempty)
    {L H X Y : Nat} (hHL : H + 1 <= L) (hlarge : Nat.factorial L + 2 <= X)
    (hrange : forall n, Membership.mem S n -> X <= n /\ n + H <= Y)
    (hwindows : forall n, Membership.mem S n ->
      2 <= ((Finset.Icc n (n + H)).filter Nat.Prime).card) :
    exists m : Nat, exists d a : Fin m -> Nat,
      S.card <= 2 * (Nat.factorial L + H) * (m + 1) /\
      (forall i, d i < a i /\ primeAt (d i) + L <= primeAt (d i + 1) /\
        primeAt (a i + 1) <= primeAt (a i) + H /\
        X <= primeAt (d i) /\ primeAt (a i + 1) <= Y) /\
      (forall i j, i < j -> a i + 1 < d j) := by
  classical
  have hchoose : forall n : Nat, exists i : Nat, Membership.mem S n ->
      n <= primeAt i /\ primeAt (i + 1) <= n + H := by
    intro n
    by_cases hn : Membership.mem S n
    next =>
      choose i hi using exists_adjacent_primes_in_window (hwindows n hn)
      exact Exists.intro i (fun _ => hi)
    next => exact Exists.intro 0 (fun h => False.elim (hn h))
  choose u hu using hchoose
  let F := Nat.factorial L
  let cell := fun n => (primeAt (u n) - 2) / F
  let T := S.image cell
  have hTp : 0 < T.card := Finset.card_pos.mpr (hS.image cell)
  let c : Fin T.card -> Nat := T.orderEmbOfFin rfl
  have hc : StrictMono c := (T.orderEmbOfFin rfl).strictMono
  have hrepresentatives : forall j : Fin T.card, exists n,
      Membership.mem S n /\ cell n = c j := by
    intro j
    exact Finset.mem_image.mp (T.orderEmbOfFin_mem rfl j)
  choose n hn hcell using hrepresentatives
  have hbig : forall n, Membership.mem S n -> F + 2 <= primeAt (u n) := by
    intro n hnS
    exact hlarge.trans ((hrange n hnS).1.trans (hu n hnS).1)
  have hb : forall j : Fin T.card,
      0 < c j /\ c j * F + L + 1 <= primeAt (u (n j)) /\
        primeAt (u (n j)) <= (c j + 1) * F + 1 := by
    intro j
    have hb := Nat.prime_factorial_cell_bounds (prime_primeAt (u (n j)))
      (hbig (n j) (hn j))
    change 0 < cell (n j) /\ cell (n j) * F + L + 1 <= primeAt (u (n j)) /\
      primeAt (u (n j)) <= (cell (n j) + 1) * F + 1 at hb
    rwa [hcell j] at hb
  have hshort : forall j : Fin T.card,
      primeAt (u (n j) + 1) <= primeAt (u (n j)) + H := by
    intro j
    have hw := hu (n j) (hn j)
    omega
  have hright : forall j : Fin T.card,
      primeAt (u (n j) + 1) <= (c j + 1) * F + 1 := by
    intro j
    have hr := Nat.short_prime_pair_same_factorial_cell
      (prime_primeAt (u (n j))) (prime_primeAt (u (n j) + 1))
      (hbig (n j) (hn j)) (hshort j) hHL
    change primeAt (u (n j) + 1) <= (cell (n j) + 1) * F + 1 at hr
    rwa [hcell j] at hr
  let m := (T.card - 1) / 2
  have hm : 2 * m + 1 <= T.card := by dsimp [m]; omega
  have hM : T.card <= 2 * m + 2 := by dsimp [m]; omega
  have hbound := Nat.prime_window_shifts_le_factorial_cells S
    (fun n => primeAt (u n)) L H (by omega)
    (fun n _ => prime_primeAt (u n)) hbig
    (fun n hn => And.intro (hu n hn).1
      ((primeAt_strictMono.monotone (Nat.le_succ (u n))).trans (hu n hn).2))
  change S.card <= (F + H) * T.card at hbound
  have hcount : S.card <= 2 * (F + H) * (m + 1) := by
    calc
      S.card <= (F + H) * T.card := hbound
      _ <= (F + H) * (2 * m + 2) := Nat.mul_le_mul_left (F + H) hM
      _ = 2 * (F + H) * (m + 1) := by
        simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm]
  have hpairs := Nat.factorial_cells_separated_gap_pairs primeAt prime_primeAt
    primeAt_strictMono (by omega : 1 <= L) hm c (fun j => u (n j)) hc
    (fun j => (hb j).1) (fun j => (hb j).2.1) hright hshort
    (fun j => (hrange (n j) (hn j)).1.trans (hu (n j) (hn j)).1)
    (fun j => (hu (n j) (hn j)).2.trans (hrange (n j) (hn j)).2)
  choose d a hda hsep using hpairs
  exact Exists.intro m (Exists.intro d (Exists.intro a
    (And.intro hcount (And.intro hda hsep))))

end PrimeFactorUnimodality
