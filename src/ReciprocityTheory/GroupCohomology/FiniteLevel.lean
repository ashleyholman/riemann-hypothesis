module

public import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GroupCohomology.InfRes
public import ReciprocityTheory.GroupCohomology.HomogIso
public import ReciprocityTheory.GroupCohomology.PrismOpZeroEval

@[expose] public section

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Topology
open scoped Pointwise

universe u

namespace FiniteLevelCohomology

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem stab_mem_nhds (M : TRep R G) [DiscreteTopology M.V] (m : M.V) :
    {a : G | M.rho a m = m} ∈ 𝓝 (1 : G) := by
  have hc : Continuous fun a : G => M.rho a m :=
    M.cont.comp (Continuous.prodMk continuous_id continuous_const)
  exact (hc.isOpen_preimage {m} (isOpen_discrete _)).mem_nhds (by simp)

end FiniteLevelCohomology

namespace FiniteLevelCohomology

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem sum_neg_one_pow (k : ℕ) :
    (1 : R) + ∑ j : Fin (k + 1), (-1 : R) ^ ((j : ℕ) + 1) = if Even k then 0 else 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc, ← add_assoc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    rcases Nat.even_or_odd k with hk | hk
    · have h1 : ¬ Even (k + 1) := Nat.not_even_iff_odd.2 (Even.add_one hk)
      rw [if_pos hk, if_neg h1, pow_succ, pow_succ, Even.neg_one_pow hk]
      ring
    · have h1 : Even (k + 1) := Odd.add_one hk
      rw [if_neg (Nat.not_even_iff_odd.2 hk), if_pos h1, pow_succ, pow_succ, Odd.neg_one_pow hk]
      ring

theorem dn_subsingleton {K : Type u} [Group K] [TopologicalSpace K] [Subsingleton K]
    (M : TRep R K) (k : ℕ) (f : (Fin k → K) → M.V) (g : Fin (k + 1) → K) :
    dn M.rho k f g = (if Even k then (0 : R) else 1) • f (fun _ => 1) := by
  have e : ∀ x : Fin k → K, f x = f (fun _ => 1) := fun x => congrArg f (Subsingleton.elim _ _)
  have hs : (∑ j : Fin (k + 1), (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)) =
      ∑ j : Fin (k + 1), (-1 : R) ^ ((j : ℕ) + 1) • f (fun _ => 1) :=
    Finset.sum_congr rfl fun j _ => by rw [e (Fin.contractNth j (· * ·) g)]
  rw [dn_apply, Subsingleton.elim (g 0) 1, map_one, e (fun i => g i.succ), hs, ← Finset.sum_smul,
    ← sum_neg_one_pow k, add_smul, one_smul]
  rfl

theorem H_succ_trivial {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [Subsingleton K] (M : TRep R K) (m : ℕ) (z : M.H (m + 1)) : z = 0 := by
  classical
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [Submodule.Quotient.mk_eq_zero]
  have hwf : ∀ g, dn M.rho (m + 1) w.1.1 g = 0 := fun g => by
    have h := congrArg (fun x : M.coch.X (m + 1 + 1) => x.1 g) w.2
    exact h
  show (w : M.coch.X (m + 1)) ∈ LinearMap.range (M.coch.d m)
  rcases Nat.even_or_odd m with hm | hm
  · have h1 : w.1.1 (fun _ => 1) = 0 := by
      have h := hwf (fun _ => 1)
      rwa [dn_subsingleton, if_neg (Nat.even_add_one.not.mpr (not_not.mpr hm)), one_smul] at h
    refine ⟨0, ?_⟩
    rw [map_zero]
    symm
    apply Subtype.ext
    funext g
    show w.1.1 g = 0
    rw [Subsingleton.elim g (fun _ => 1)]
    exact h1
  · refine ⟨⟨fun _ => w.1.1 (fun _ => 1), ?_⟩, ?_⟩
    · exact continuous_const
    · apply Subtype.ext
      funext g
      show dn M.rho m (fun _ => w.1.1 (fun _ => 1)) g = w.1.1 g
      rw [dn_subsingleton, if_neg (Nat.not_even_iff_odd.mpr hm), one_smul]
      rw [Subsingleton.elim g (fun _ => 1)]

end FiniteLevelCohomology

end ReciprocityTheory.Coh
