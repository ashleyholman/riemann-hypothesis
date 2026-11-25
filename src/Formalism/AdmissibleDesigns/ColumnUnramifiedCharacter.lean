module

public import Formalism.AdmissibleDesigns.CohomZeroEquivContinuous
public import Formalism.AdmissibleDesigns.TheoremN5OfNormalizedItems
public import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice
public import Formalism.AdmissibleDesigns.CharacterTrivialWhereLattice
public import Formalism.AdmissibleDesigns.KernelLengthHigherColumns
public import Formalism.AdmissibleDesigns.MemImageOfTensorSum
public import Formalism.AdmissibleDesigns.RankReductionIdempotentOne
public import Formalism.AdmissibleDesigns.EKSymmCont
import Formalism.AdmissibleDesigns.PiEquiv2
import Formalism.WachLatticeTwists.SplitClassesAll.Statement

@[expose] public section

noncomputable section

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]
open Formalism.BasicNotions Classical
namespace Formalism.MainNotions.N.KOrb
open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem contW_rec (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (l : K.Col i dc) :
    KDim.ContW (i := i) (dc := dc) (ρ := ρ) (π := π) l :=
  contW_of i dc ρ π (K.Norm.rhoCont_of i r ρ π hd hc) l

end Formalism.MainNotions.N.KOrb
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]
open Formalism.BasicNotions Classical
namespace Formalism.MainNotions.N.KHf
open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)

theorem exists_Lx {Pe : Type} [AddCommGroup Pe] [Module R' Pe] [Module (D.nd.O i) Pe] [SMulCommClass R' (D.nd.O i) Pe]
    {PE : Type} [AddCommGroup PE] [Module R' PE] [Module (D.nd.O i) PE] [SMulCommClass R' (D.nd.O i) PE]
    (hPe : ∀ (c : D.nd.O i) (m : Pe), c • m = (algebraMap (D.nd.O i) R' c) • m)
    (hPE : ∀ (c : D.nd.O i) (m : PE), c • m = (algebraMap (D.nd.O i) R' c) • m)
    (j : ℕ → ℕ) (x' : X') (l : K.Col i dc)
    (hO : letI := evalModO i (R' := R') x'
      haveI := evalTower i (R' := R') x'
      OrbC i dc (repE i dc r χ x' (K.colIdx i dc l)))
    (hdim : DimLx i dc r χ j x' l) :
    ∃ Lx : Submodule (FractionRing (D.nd.O i)) (↥(Γn i dc (K.colIdx i dc l)) → EvalSp (D.nd.O i) d R' x'),
      LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x') r χ
        (Γn i dc (K.colIdx i dc l))) ≤ Lx ∧
      (∀ (f : Pe →ₗ[R'] EvalSp (D.nd.O i) d R' x')
        (z : coZ1s (resRep (uRep (D.nd.O i) (M := Pe) r χ) (Γn i dc (K.colIdx i dc l)))),
        Submodule.mkQ _ z ∈ Hfe₁ i dc r χ (Pe := Pe) l →
        (fun g : Γn i dc (K.colIdx i dc l) => f ((z : Γn i dc (K.colIdx i dc l) → Pe) g)) ∈ Lx) ∧
      (∀ (f : PE →ₗ[R'] EvalSp (D.nd.O i) d R' x')
        (z : coZ1s (resRep (uRep (D.nd.O i) (M := PE) r χ) (Γn i dc (K.colIdx i dc l)))),
        Submodule.mkQ _ z ∈ Hfe₁ i dc r χ (Pe := PE) l →
        (fun g : Γn i dc (K.colIdx i dc l) => f ((z : Γn i dc (K.colIdx i dc l) → PE) g)) ∈ Lx) ∧
      Module.rank (FractionRing (D.nd.O i))
          (Lx ⧸ (LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x') r χ
            (Γn i dc (K.colIdx i dc l)))).comap Lx.subtype) ≤
        (j (K.colIdx i dc l) + Module.finrank (FractionRing (D.nd.O i))
          (LinearMap.ker (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x') r χ
            (Γn i dc (K.colIdx i dc l)))) : ℕ) := by
  refine ⟨Lx i dc r χ x' l, ?_, ?_, ?_, hdim⟩
  · apply colD_le_Lx <;> assumption
  · intro f z hz
    apply comp_mem_Lx <;> assumption
  · intro f z hz
    apply comp_mem_Lx <;> assumption

end Formalism.MainNotions.N.KHf
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]
open Finset Classical Formalism.BasicNotions
namespace Formalism.MainNotions.N.K.StA
open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St
attribute [local instance 2000] Topo.fracTopology Topo.rTopology

theorem r_pos (D : D7) : 0 < D.R.r := by
  have h := D.R.m_add_three_le_k
  show 0 < D.R.k + D.R.m - 1
  omega

theorem card_pos (D : D7) : 0 < Fintype.card (Fin D.R.nV) := by
  rw [Fintype.card_fin]
  have h := D.R.m_add_three_le_k
  show 0 < D.R.k + D.R.m - 1 + D.R.t
  omega

theorem jN_eq {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (dc : TruncatedSeriesCountingIdentities.Decl D i) : jN i ρ π dc = KHf.jK i dc ρ π := rfl

theorem leftId_alg {O : Type} [CommRing O] {A : Type} [Ring A] [Algebra O A] (x : A) (c : O) (m : LeftId O x) :
    c • m = (algebraMap O A c) • m := by
  exact Subtype.ext (Algebra.smul_def c m.1)

section Cols

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem colUz : ∀ l (g : decs D.host.E (Aw i dc) (colIdx i dc l)),
    (((KFin.uz i dc Dd.δO l : decs D.host.E (Aw i dc) (colIdx i dc l) → ↥(Ideal.span {Dd.δO})) g :
      ↥(Ideal.span {Dd.δO})) : D.nd.O i) = Dd.δO * KFin.u i dc l g := by
  intro l g
  first
  | (show Dd.δO * KFin.uCol i dc l g = Dd.δO * KFin.u i dc l g
     rw [KFin.u, dite_eq_left (show ((g : GE D.nd)) ∈ KFin.Γc i dc l from g.2)])

theorem column_unramified_character : (∀ l, ∀ g ∈ QS.I i dc (colIdx i dc l), KFin.u i dc l (g : GE D.nd) = 0) ∧
    (∀ l, ∃ g ∈ (decs D.host.E (Aw i dc)) (colIdx i dc l), KFin.u i dc l g = 1) :=
  ⟨fun l => KFin.u_I i dc l (KUnr.unrHom i dc l), fun l => KFin.u_one i dc l (KUnr.unrHom i dc l)⟩

variable [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem colLx_of_ringDef
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (hBK : TruncatedSeriesCountingIdentities.admBK i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i)
    (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hCr : ∀ x' l, KDim.CrysX i dc Dd.r Dd.χ x' l) (hNeg : ∀ x' l, KDim.NegX i dc Dd.r Dd.χ ρ π x' l)
    (hFin : ∀ x' l, KDim.FinX i dc Dd.r Dd.χ x' l) (hCrW : ∀ l, KDim.CrysW i dc ρ π l) :
    ∀ x' : Dd.X', Dd.p x' ∉ (D.nd.Z i : Set (D.nd.X i)) → ∀ l : Col i dc,
      ∃ Lx : Submodule (FractionRing (D.nd.O i))
          ((decs D.host.E (Aw i dc)) (colIdx i dc l) → EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x'),
        LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
          ((decs D.host.E (Aw i dc)) (colIdx i dc l))) ≤ Lx ∧
        (∀ (f : LeftId (D.nd.O i) Dd.e₁ →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.e₁) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.e₁) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.e₁) g)) ∈ Lx) ∧
        (∀ (f : LeftId (D.nd.O i) Dd.E →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.E) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.E) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.E) g)) ∈ Lx) ∧
        Module.rank (FractionRing (D.nd.O i))
            (Lx ⧸ (LinearMap.range
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))).comap Lx.subtype) ≤
          (jN i ρ π dc (colIdx i dc l) + Module.finrank (FractionRing (D.nd.O i))
            (LinearMap.ker
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))) : ℕ) := by
  intro x' _ l
  have hO := KOrb.orbC_repE i dc r π g0 eB e₁ s Dd hD hc x' (colIdx i dc l)
  have hdim : KHf.DimLx i dc Dd.r Dd.χ (KHf.jK i dc ρ π) x' l :=
    KDim.dimLx_of_font i dc Dd.r Dd.χ ρ π r x' l (card_pos D) (r_pos D) hBK hG2 hFont
      (KDim.contX_of_orbC i dc Dd.r Dd.χ x' l hO) (hCr x' l) (hNeg x' l) (hFin x' l) (hCrW l)
      (KOrb.contW_rec i dc r ρ π hDec hc l)
  rw [jN_eq]
  exact KHf.exists_Lx i dc Dd.r Dd.χ (leftId_alg Dd.e₁) (leftId_alg Dd.E) (KHf.jK i dc ρ π) x' l hO hdim

end Cols
end Formalism.MainNotions.N.K.StA
end

end
