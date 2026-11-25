module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ResidueCharMemLevelPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PhiCondOfFiniteH1

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement

private theorem fin_above {n : ℕ} (hn : n ≠ 0) :
    {v : HeightOneSpectrum (𝓞 ℚ) | ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((n : ℕ) : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_span_singleton]; exact hv

end UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.phiGam :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → CohomologyHyp → PhiCond D.Gam l := by
  intro Ω _ _ _ l hl c D hD hP
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hfin : D.SP.Finite := by
    refine (D.S.finite_toSet.biUnion fun p hp => fin_above (hD.S_prime p hp).ne_zero).subset ?_
    rintro v ⟨p, hp, hv⟩
    exact Set.mem_biUnion hp hv
  have hS : ContainsAbove hfin.toFinset l := fun v hv => hfin.mem_toFinset.2 ⟨l, hD.l_mem, hv⟩
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have key : PhiCond (GS Ω (hfin.toFinset : Set (HeightOneSpectrum (𝓞 ℚ)))) (l ^ 1) :=
    UpperTheory.V.Alg.phiCond_of_finite_H1 (l ^ 1) fun M _ _ _ _ _ ρ hρ => by
      obtain ⟨-, f1, -⟩ := hP.gf ℚ Ω l 1 M hfin.toFinset ρ one_pos hS hρ
      exact f1
  rw [pow_one, hfin.coe_toFinset] at key
  exact key
