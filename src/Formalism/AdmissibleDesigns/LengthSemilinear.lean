module

public import Formalism.AdmissibleDesigns.NonemptyPl
public import Formalism.SharpRestriction.LevelLetterCocycles.GoodCongruenceDataOf
public import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.Statement
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero
public import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
public import Formalism.SharpRestriction.LevelLetterCocycles.RingDataOfIdempotents
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.AdmissibleDesigns.CharacterTrivialWhereLattice
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

section
open Formalism.BasicNotions Classical
namespace Formalism.MainNotions.N.K
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.MainNotions Formalism.MainNotions.N
section Arith

def qU (e : ℕ) (x : ℕ∞) : ℚ := (x.toNat : ℚ) / e

theorem qU_mono {e : ℕ} {x y : ℕ∞} (h : x ≤ y) (hy : y ≠ ⊤) : qU e x ≤ qU e y := by
  unfold qU
  have h1 : x.toNat ≤ y.toNat := ENat.toNat_le_toNat h hy
  have h2 : (x.toNat : ℚ) ≤ y.toNat := by exact_mod_cast h1
  gcongr

theorem qU_eO_mul {e : ℕ} (he : e ≠ 0) (x : ℕ∞) : qU e ((e : ℕ∞) * x) = (x.toNat : ℚ) := by
  induction x using ENat.recTopCoe with
  | top =>
    rw [ENat.mul_top (by exact_mod_cast he)]
    simp only [qU, ENat.toNat_top, Nat.cast_zero, zero_div]
  | coe n =>
    have he0 : (e : ℚ) ≠ 0 := by exact_mod_cast he
    rw [← Nat.cast_mul]
    simp only [qU, ENat.toNat_natCast]
    push_cast
    first | (field_simp; ring) | field_simp

theorem inequality_of_finite_terms (e : ℕ) (he : e ≠ 0) (eO : ℕ∞) (heO : eO = e) (lhs : ℕ∞) (what₂ cols qs : Finset ℕ)
    (rowLen h0d z : ℕ → ℕ∞) (e' j deg : ℕ → ℕ) (vδ s H0 : ℕ∞) (Sha : ℕ → ℕ∞) (hE t cB Nn : ℕ)
    (hR : ∀ w ∈ what₂, rowLen w ≠ ⊤) (hH : ∀ w ∈ cols, h0d w ≠ ⊤) (hv : vδ ≠ ⊤) (hs : s ≠ ⊤)
    (hSha : ∀ k ∈ Finset.Ioo 0 t, Sha k ≠ ⊤) (hH0 : H0 ≠ ⊤) (hz : ∀ w ∈ qs, z w ≠ ⊤)
    (hd : lhs ≤
      ∑ w ∈ what₂, rowLen w +
        ∑ w ∈ cols, (eO * (e' w : ℕ∞) + (j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ + h0d w) + s +
        ∑ k ∈ Finset.Ioo 0 t, Sha k + eO * (hE : ℕ∞) +
        (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
        4 * ((Nn : ℕ∞) + t) * ((cols.card : ℕ∞) + 1) * vδ +
        (t : ℕ∞) * (cols.card : ℕ∞) * H0 + (t : ℕ∞) * ∑ w ∈ qs, z w) :
    qU e lhs ≤
      ∑ w ∈ what₂, qU e (rowLen w) +
        ∑ w ∈ cols, ((e' w : ℚ) + (j w : ℚ) * ((e' w : ℚ) + qU e vδ) + 2 * qU e vδ + qU e (h0d w)) +
        qU e s + ∑ k ∈ Finset.Ioo 0 t, qU e (Sha k) + (hE : ℚ) +
        (t : ℚ) * (∑ w ∈ what₂, ((deg w : ℚ) + 2) * (cB : ℚ)) +
        4 * ((Nn : ℚ) + t) * ((cols.card : ℚ) + 1) * qU e vδ +
        (t : ℚ) * (cols.card : ℚ) * qU e H0 + (t : ℚ) * ∑ w ∈ qs, qU e (z w) := by
  subst heO
  obtain ⟨v, rfl⟩ := ENat.ne_top_iff_exists.mp hv
  obtain ⟨sn, rfl⟩ := ENat.ne_top_iff_exists.mp hs
  obtain ⟨h0n, rfl⟩ := ENat.ne_top_iff_exists.mp hH0
  have h1 : ∑ w ∈ what₂, rowLen w = ((∑ w ∈ what₂, (rowLen w).toNat : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl fun w hw => (ENat.natCast_toNat (hR w hw)).symm
  have h2 : ∑ w ∈ cols, ((e : ℕ∞) * (e' w : ℕ∞) + (j w : ℕ∞) * ((e : ℕ∞) * (e' w : ℕ∞) + (v : ℕ∞)) +
      2 * (v : ℕ∞) + h0d w) =
      ((∑ w ∈ cols, (e * e' w + j w * (e * e' w + v) + 2 * v + (h0d w).toNat) : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [← ENat.natCast_toNat (hH w hw)]
    simp only [ENat.toNat_natCast]
    push_cast; ring
  have h3 : ∑ k ∈ Finset.Ioo 0 t, Sha k = ((∑ k ∈ Finset.Ioo 0 t, (Sha k).toNat : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl fun k hk => (ENat.natCast_toNat (hSha k hk)).symm
  have h4 : ∑ w ∈ qs, z w = ((∑ w ∈ qs, (z w).toNat : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl fun w hw => (ENat.natCast_toNat (hz w hw)).symm
  have h5 : ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) = ((∑ w ∈ what₂, (deg w + 2) : ℕ) : ℕ∞) := by
    push_cast; rfl
  rw [h1, h2, h3, h4, h5] at hd
  norm_cast at hd
  have hl : lhs ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hd
  obtain ⟨L, rfl⟩ := ENat.ne_top_iff_exists.mp hl
  have hL := (ENat.natCast_le_natCast).mp hd
  have hq := (Nat.cast_le (α := ℚ)).mpr hL
  have heq : (e : ℚ) ≠ 0 := by exact_mod_cast he
  have hs1 : ∑ w ∈ what₂, qU e (rowLen w) = ((∑ w ∈ what₂, (rowLen w).toNat : ℕ) : ℚ) / e := by
    rw [Nat.cast_sum, Finset.sum_div]; rfl
  have hs2 : ∑ w ∈ cols, ((e' w : ℚ) + (j w : ℚ) * ((e' w : ℚ) + qU e (v : ℕ∞)) + 2 * qU e (v : ℕ∞) +
      qU e (h0d w)) =
      ((∑ w ∈ cols, (e * e' w + j w * (e * e' w + v) + 2 * v + (h0d w).toNat) : ℕ) : ℚ) / e := by
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [qU, ENat.toNat_natCast]
    push_cast
    field_simp
  have hs3 : ∑ k ∈ Finset.Ioo 0 t, qU e (Sha k) = ((∑ k ∈ Finset.Ioo 0 t, (Sha k).toNat : ℕ) : ℚ) / e := by
    rw [Nat.cast_sum, Finset.sum_div]; rfl
  have hs4 : ∑ w ∈ qs, qU e (z w) = ((∑ w ∈ qs, (z w).toNat : ℕ) : ℚ) / e := by
    rw [Nat.cast_sum, Finset.sum_div]; rfl
  have hs5 : ∑ w ∈ what₂, ((deg w : ℚ) + 2) * (cB : ℚ) = ((∑ w ∈ what₂, (deg w + 2) : ℕ) : ℚ) * cB := by
    rw [Nat.cast_sum, Finset.sum_mul]; push_cast; rfl
  rw [hs1, hs2, hs3, hs4, hs5]
  simp only [qU, ENat.toNat_natCast]
  rw [div_le_iff₀ (by positivity)]
  refine hq.trans (le_of_eq ?_)
  push_cast
  field_simp

end Arith

section Rec

variable {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i)

open Formalism.MainNotions.N.Glob Formalism.BasicNotions.Loc

def eON : ℕ∞ := Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {((D.nd.l i : ℕ) : D.nd.O i)})

def jN (n : ℕ) : ℕ :=
  if h : plOf i dc n ∈ placesOver D.host.E (D.nd.l i) then Br.jW D.loc D.nbr i (plOf i dc n) h ρ π else 0

def e'N (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (n : ℕ) : ℕ := e' (plOf i dc n)

def sN : ℕ∞ := Module.length (D.nd.O i) ↥(Br.selPi D.loc D.nbr i ρ π)

def ShaN (e : ℕ) : ℕ∞ := eON i * Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ)

def twistInvariantsLength (w : HeightOneSpectrum (𝓞 D.host.E)) : ℕ∞ :=
  Module.length (D.nd.O i) ↥(Representation.invariants ((Br.WKO i ρ π).comp (decS D.nd w)))

def invLen (w : HeightOneSpectrum (𝓞 D.host.E)) (e : ℕ) : ℕ∞ :=
  Module.length (D.nd.O i) ↥(Representation.invariants ((KOtw D.nd i (e : ℤ)).comp (decS D.nd w)))

def invariantsLengthSup : ℕ∞ := (dc.col ×ˢ Finset.Ioo 0 D.R.t).sup fun p => invLen i p.1 p.2

def zetaN (n : ℕ) : D.nd.O i := D.nd.zeta i (plOf i dc n)

def LeTwistInvariantsAtColumns (h0d : ℕ → ℕ∞) : Prop := ∀ n ∈ colsN i dc, h0d n ≤ twistInvariantsLength i ρ π (plOf i dc n)

def TieRow (rowLen : ℕ → ℕ∞) (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) : Prop :=
  ∀ n ∈ rowsN i dc, rowLen n ≠ ⊤ ∧ ((rowLen n).toNat : ℚ) ≤ ((eON i).toNat : ℚ) * lenRow (plOf i dc n)

def FiniteTwistInvariants : Prop := ∀ w ∈ dc.col, twistInvariantsLength i ρ π w < ⊤

def FiniteCharacterInvariants : Prop := ∀ w ∈ dc.col, ∀ e ∈ Finset.Ioo 0 D.R.t, invLen i w e < ⊤

def ZetaNe : Prop := ∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1

end Rec

section Sel

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Finset

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G] [TopologicalSpace G]

def selRho (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (what₂ : Finset ℕ)
    (F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    {Vo : Type} (Io : Vo → Subgroup G) : Submodule O (H1z (uRep O (M := M) r χ)) :=
  (lcH1 (uRep O (M := M) r χ) ⊓ ⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
    ⨅ w ∈ what₂ ∪ univ.image colIdx, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))

def selChi (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (what₂ qs : Finset ℕ)
    (F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    {Vo VS : Type} (Io : Vo → Subgroup G) (IS : VS → Subgroup G) : Submodule O (H1z (uRep O (M := M) r χ)) :=
  (lcH1 (uRep O (M := M) r χ) ⊓ (⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
      ⨅ v, unrH1 (uRep O (M := M) r χ) (IS v)) ⊓
    ⨅ w ∈ what₂ ∪ qs ∪ univ.image colIdx, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))

def InjTie {H H' : Type} [AddCommGroup H] [Module O H] [AddCommGroup H'] [Module O H']
    (S : Submodule O H) (S' : Submodule O H') : Prop :=
  ∃ f : ↥S →ₗ[O] ↥S', Function.Injective f

theorem length_le_of_injTie {H H' : Type} [AddCommGroup H] [Module O H] [AddCommGroup H'] [Module O H']
    {S : Submodule O H} {S' : Submodule O H'} (h : InjTie S S') :
    Module.length O ↥S ≤ Module.length O ↥S' := by
  obtain ⟨f, hf⟩ := h
  exact Module.length_le_of_injective f hf

end Sel

section SelRec

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology

variable {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  {A T' G : Type} [Ring A] [Algebra (D.nd.O i) A] [CommRing T'] [Algebra T' A] [Group G] [TopologicalSpace G]

def TieSel1 (M : Type) [AddCommGroup M] [Module A M] [Module (D.nd.O i) M] [SMulCommClass A (D.nd.O i) M]
    (r : G →* A) (χ : G →* T'ˣ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (Dw : ℕ → Subgroup G) (what₂ : Finset ℕ)
    (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := M) r χ) (Dw w))))
    {Vo : Type} (Io : Vo → Subgroup G) : Prop :=
  InjTie (selRho M r χ colIdx Dw what₂ F Io) (Br.selPi D.loc D.nbr i ρ π)

theorem selRho_le_sN (M : Type) [AddCommGroup M] [Module A M] [Module (D.nd.O i) M]
    [SMulCommClass A (D.nd.O i) M]
    (r : G →* A) (χ : G →* T'ˣ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (Dw : ℕ → Subgroup G) (what₂ : Finset ℕ)
    (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := M) r χ) (Dw w))))
    {Vo : Type} (Io : Vo → Subgroup G) (h : TieSel1 i ρ π M r χ colIdx Dw what₂ F Io) :
    Module.length (D.nd.O i) ↥(selRho M r χ colIdx Dw what₂ F Io) ≤ sN i ρ π := length_le_of_injTie h

def TieSel2 (M : Type) [AddCommGroup M] [Module A M] [Module (D.nd.O i) M] [SMulCommClass A (D.nd.O i) M]
    (r : G →* A) (χ : G →* T'ˣ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (Dw : ℕ → Subgroup G) (what₂ qs : Finset ℕ)
    (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := M) r χ) (Dw w))))
    {Vo VS : Type} (Io : Vo → Subgroup G) (IS : VS → Subgroup G) (c : ℕ) : Prop :=
  Module.length (D.nd.O i) ↥(selChi M r χ colIdx Dw what₂ qs F Io IS) ≤ ShaN i (c - 1)

end SelRec

section N9Rec

variable {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i)

open Formalism.MainNotions.N.Glob Formalism.BasicNotions.Loc

theorem eON_eq : ∃ e : ℕ, e ≠ 0 ∧ eON i = e := by
  obtain ⟨e, he0, he⟩ := Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.exists_eO D.nd i
  exact ⟨e, he0, by unfold eON; rw [Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span, he]⟩

theorem lenUnit_eq_qU (M : Type) [AddCommGroup M] [Module (D.nd.O i) M] :
    lenUnit (O := D.nd.O i) (D.nd.l i) M = qU (eON i).toNat (Module.length (D.nd.O i) M) := rfl

theorem row_mem_plSet {v : HeightOneSpectrum (𝓞 D.host.E)} (h : v ∈ dc.row) : v ∈ plSet i dc := by
  unfold plSet
  exact Finset.mem_union_left _ (Finset.mem_union_left _ h)

theorem col_mem_plSet {v : HeightOneSpectrum (𝓞 D.host.E)} (h : v ∈ dc.col) : v ∈ plSet i dc := by
  unfold plSet
  exact Finset.mem_union_left _ (Finset.mem_union_right _ h)

theorem q_mem_plSet {v : HeightOneSpectrum (𝓞 D.host.E)} (h : v ∈ D.nd.Q i) : v ∈ plSet i dc := by
  unfold plSet
  exact Finset.mem_union_right _ h

theorem sum_rowsN {β : Type} [AddCommMonoid β] (f : ℕ → β) :
    ∑ n ∈ rowsN i dc, f n = ∑ v ∈ dc.row, f (idx i dc v) := by
  unfold rowsN
  exact Finset.sum_image (by
    intro x hx y hy hxy
    exact idx_inj i dc (row_mem_plSet i dc hx) (row_mem_plSet i dc hy) hxy)

theorem sum_qsN {β : Type} [AddCommMonoid β] (f : ℕ → β) :
    ∑ n ∈ qsN i dc, f n = ∑ v ∈ D.nd.Q i, f (idx i dc v) := by
  unfold qsN
  exact Finset.sum_image (by
    intro x hx y hy hxy
    exact idx_inj i dc (q_mem_plSet i dc hx) (q_mem_plSet i dc hy) hxy)

private theorem image_colIdx_eq_image_idx : Finset.univ.image (colIdx i dc) = dc.col.image (idx i dc) := by
  unfold colIdx
  ext n
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨l.1, l.2, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

theorem sum_cols {β : Type} [AddCommMonoid β] (f : ℕ → β) :
    ∑ n ∈ Finset.univ.image (colIdx i dc), f n = ∑ v ∈ dc.col, f (idx i dc v) := by
  rw [image_colIdx_eq_image_idx i dc]
  exact Finset.sum_image (by
    intro x hx y hy hxy
    exact idx_inj i dc (col_mem_plSet i dc hx) (col_mem_plSet i dc hy) hxy)

theorem card_cols : (Finset.univ.image (colIdx i dc)).card = dc.col.card := by
  rw [image_colIdx_eq_image_idx i dc]
  exact Finset.card_image_of_injOn (by
    intro x hx y hy hxy
    exact idx_inj i dc (col_mem_plSet i dc hx) (col_mem_plSet i dc hy) hxy)

theorem cols_eq : Finset.univ.image (colIdx i dc) = colsN i dc := by
  unfold colsN
  exact image_colIdx_eq_image_idx i dc

theorem plOf_mem_col {n : ℕ} (hn : n ∈ colsN i dc) : plOf i dc n ∈ dc.col := by
  unfold colsN at hn
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hn
  rw [plOf_idx i dc (col_mem_plSet i dc hv)]
  exact hv

theorem le_H0N {x : ℕ∞} {n : ℕ} (hn : n ∈ colsN i dc) {k : ℕ} (hk : k ∈ Finset.Ioo 0 D.R.t)
    (h : x ≤ invLen i (plOf i dc n) k) : x ≤ invariantsLengthSup i dc := by
  refine h.trans ?_
  unfold invariantsLengthSup
  have hm : (plOf i dc n, k) ∈ dc.col ×ˢ Finset.Ioo 0 D.R.t :=
    Finset.mem_product.2 ⟨plOf_mem_col i dc hn, hk⟩
  have h2 := Finset.le_sup (f := fun p : HeightOneSpectrum (𝓞 D.host.E) × ℕ => invLen i p.1 p.2) hm
  exact h2

theorem invariants_length_sup_ne_top (hF : FiniteCharacterInvariants i dc) : invariantsLengthSup i dc ≠ ⊤ := by
  rw [← lt_top_iff_ne_top]
  unfold invariantsLengthSup
  rw [Finset.sup_lt_iff (bot_lt_top : (⊥ : ℕ∞) < ⊤)]
  rintro ⟨w, k⟩ hp
  rw [Finset.mem_product] at hp
  exact hF w hp.1 k hp.2

theorem qU_H0N_le : qU (eON i).toNat (invariantsLengthSup i dc) ≤ h0 D.nd i dc.col := by
  unfold Formalism.MainNotions.N.h0
  rcases (dc.col ×ˢ Finset.Ioo 0 D.R.t).eq_empty_or_nonempty with hs | hs
  · unfold invariantsLengthSup
    rw [hs]
    simp [qU]
  · obtain ⟨p, hp, hpeq⟩ := Finset.exists_mem_eq_sup _ hs (fun p => invLen i p.1 p.2)
    have hH : invariantsLengthSup i dc = invLen i p.1 p.2 := by
      unfold invariantsLengthSup
      exact hpeq
    rw [hH]
    have hm : qU (eON i).toNat (invLen i p.1 p.2) ∈ Finset.image (fun p => lenUnit (D.nd.l i)
        ↥(Representation.invariants (MonoidHom.comp (KOtw D.nd i ↑p.2) (decS D.nd p.1))))
        (dc.col ×ˢ Finset.Ioo 0 D.R.t) := Finset.mem_image.2 ⟨p, hp, rfl⟩
    obtain ⟨m, hmax⟩ := Finset.max_of_mem hm
    rw [hmax, WithBot.unbotD_coe]
    exact Finset.le_max_of_eq hm hmax

theorem vcc_eq_qU : D.nd.vcc i π =
    qU (eON i).toNat (Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π)) := rfl

theorem sPi_eq_qU : Br.sPi D.loc D.nbr i ρ π = qU (eON i).toNat (sN i ρ π) := rfl

theorem twist_invariants_unit_change (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Br.h0W i w ρ π = qU (eON i).toNat (twistInvariantsLength i ρ π w) := rfl

theorem qU_ShaN {k : ℕ} (hk : k ∈ Finset.Ioo 0 D.R.t)
    (hf : Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (k : ℤ) < ⊤) :
    qU (eON i).toNat (ShaN i k) = D.what₂.shaLen (D.nd.l i) k := by
  obtain ⟨e, he0, he⟩ := eON_eq i
  unfold ShaN
  rw [he, ENat.toNat_natCast, qU_eO_mul he0]
  obtain ⟨hk0, hkt⟩ := Finset.mem_Ioo.mp hk
  rw [D.nd.sha_eq (D.nd.l i) k hk0 hkt _ (ENat.natCast_toNat hf.ne).symm]

theorem lenUnit_zeta (v : HeightOneSpectrum (𝓞 D.host.E)) :
    lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1}) =
      qU (eON i).toNat (IsDiscreteValuationRing.addVal (D.nd.O i) (D.nd.zeta i v - 1)) := by
  rw [lenUnit_eq_qU, Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span]

theorem zeta_ne_top (hz : ZetaNe i) {v : HeightOneSpectrum (𝓞 D.host.E)} (hv : v ∈ D.nd.Q i) :
    IsDiscreteValuationRing.addVal (D.nd.O i) (D.nd.zeta i v - 1) ≠ ⊤ := by
  rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  exact sub_ne_zero.mpr (hz v hv)

theorem card_first_block : Fintype.card {a // RepresentationBoundsCohomology.blk D.R a = 0} = D.R.r :=
  (Fintype.card_congr (Formalism.MainNotions.N.RepresentationBoundsCohomology.blockZeroEquiv D.R.r D.R.t).symm).trans (Fintype.card_fin _)

end N9Rec

section N9Main

variable {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i)

open Formalism.MainNotions.N.Glob Formalism.BasicNotions.Loc

theorem qU_vdel {vδ : ℕ∞}
    (hvδ : vδ = eON i * ((∑ k ∈ Finset.Ioo 0 D.R.t, (D.nd.s0 i + padicValNat (D.nd.l i) k) : ℕ) : ℕ∞)) :
    qU (eON i).toNat vδ = D.nd.vdel i := by
  unfold Formalism.BasicNotions.NData.vdel
  obtain ⟨e, he, hE⟩ := eON_eq i
  rw [hvδ, hE, ENat.toNat_natCast, qU_eO_mul he, ENat.toNat_natCast]
  push_cast
  first | rfl

theorem selmer_length_inequality (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ)
    (cB : ℕ) (rowLen h0d : ℕ → ℕ∞) (vδ : ℕ∞) (Nn : ℕ)
    (hvδ : vδ = eON i * ((∑ k ∈ Finset.Ioo 0 D.R.t, (D.nd.s0 i + padicValNat (D.nd.l i) k) : ℕ) : ℕ∞))
    (hN : Nn = D.R.r)
    (hd : Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π) ≤
      ∑ w ∈ rowsN i dc, rowLen w +
        ∑ w ∈ Finset.univ.image (colIdx i dc), (eON i * (e'N i dc e' w : ℕ∞) +
          (jN i ρ π dc w : ℕ∞) * (eON i * (e'N i dc e' w : ℕ∞) + vδ) + 2 * vδ + h0d w) + sN i ρ π +
        ∑ e ∈ Finset.Ioo 0 D.R.t, ShaN i e +
        eON i * (padicValNat (D.nd.l i) (classNumber D.host.E) : ℕ∞) +
        (D.R.t : ℕ∞) * eON i * (cB : ℕ∞) * ∑ w ∈ rowsN i dc, ((ReciprocityTheory.Gal.locDeg (plOf i dc w) : ℕ∞) + 2) +
        4 * ((Nn : ℕ∞) + D.R.t) * (((Finset.univ.image (colIdx i dc)).card : ℕ∞) + 1) * vδ +
        (D.R.t : ℕ∞) * ((Finset.univ.image (colIdx i dc)).card : ℕ∞) * invariantsLengthSup i dc +
        (D.R.t : ℕ∞) * ∑ w ∈ qsN i dc, IsDiscreteValuationRing.addVal (D.nd.O i) (zetaN i dc w - 1))
    (hT4 : TieRow i dc rowLen lenRow) (hT3 : LeTwistInvariantsAtColumns i ρ π dc h0d) (hF1 : FiniteTwistInvariants i ρ π dc)
    (hF2 : FiniteCharacterInvariants i dc) (hz : ZetaNe i) (hs : Br.sFin D.loc D.nbr i ρ π)
    (hsha : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) :
    D.nd.vcc i π ≤
      (∑ w ∈ dc.row ∪ dc.col, TruncatedSeriesCountingIdentities.lenW i ρ π dc lenRow e' w) + Br.sPi D.loc D.nbr i ρ π +
      (∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e) +
      (padicValNat (D.nd.l i) (Formalism.MainNotions.N.hE D.host) : ℚ) +
      (D.R.t : ℚ) * (∑ w ∈ dc.row, ((Formalism.MainNotions.N.locDeg D.host.E w : ℚ) + 2) * (cB : ℚ)) +
      4 * (D.R.nV : ℚ) * ((dc.col.card : ℚ) + 1) * D.nd.vdel i +
      (D.R.t : ℚ) * (dc.col.card : ℚ) * h0 D.nd i dc.col +
      (D.R.t : ℚ) * (∑ v ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i)
        (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1})) := by
  obtain ⟨e, he0, he⟩ := eON_eq i
  have hEt : (eON i).toNat = e := by rw [he, ENat.toNat_natCast]
  have hEpos : (0 : ℚ) < ((eON i).toNat : ℚ) := by rw [hEt]; exact_mod_cast Nat.pos_of_ne_zero he0

  have hR : ∀ w ∈ rowsN i dc, rowLen w ≠ ⊤ := fun w hw => (hT4 w hw).1
  have hH : ∀ w ∈ Finset.univ.image (colIdx i dc), h0d w ≠ ⊤ := by
    intro n hn
    rw [cols_eq] at hn
    exact ne_top_of_le_ne_top (hF1 _ (plOf_mem_col i dc hn)).ne (hT3 n hn)
  have hv : vδ ≠ ⊤ := by rw [hvδ, he, ← Nat.cast_mul]; exact ENat.natCast_ne_top _
  have hs' : sN i ρ π ≠ ⊤ := (show sN i ρ π < ⊤ from hs).ne
  have hSha : ∀ k ∈ Finset.Ioo 0 D.R.t, ShaN i k ≠ ⊤ := by
    intro k hk
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (hsha k hk).ne
    unfold ShaN
    rw [← hm, he, ← Nat.cast_mul]
    exact ENat.natCast_ne_top _
  have hz' : ∀ n ∈ qsN i dc, IsDiscreteValuationRing.addVal (D.nd.O i) (zetaN i dc n - 1) ≠ ⊤ := by
    intro n hn
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hn
    unfold zetaN
    rw [plOf_idx i dc (q_mem_plSet i dc hv)]
    exact zeta_ne_top i hz hv
  have key := inequality_of_finite_terms e he0 (eON i) he _ (rowsN i dc) (Finset.univ.image (colIdx i dc)) (qsN i dc) rowLen h0d
    (fun w => IsDiscreteValuationRing.addVal (D.nd.O i) (zetaN i dc w - 1)) (e'N i dc e') (jN i ρ π dc)
    (fun w => ReciprocityTheory.Gal.locDeg (plOf i dc w)) vδ (sN i ρ π) (invariantsLengthSup i dc) (ShaN i)
    (padicValNat (D.nd.l i) (classNumber D.host.E)) D.R.t cB Nn hR hH hv hs' hSha (invariants_length_sup_ne_top i dc hF2) hz' hd
  rw [← hEt] at key
  rw [vcc_eq_qU]

  have hvd := qU_vdel i hvδ
  have A0 : ∑ w ∈ dc.row ∪ dc.col, TruncatedSeriesCountingIdentities.lenW i ρ π dc lenRow e' w =
      ∑ w ∈ dc.row, lenRow w + ∑ w ∈ dc.col, TruncatedSeriesCountingIdentities.lenW i ρ π dc lenRow e' w := by
    rw [Finset.sum_union dc.disj]
    congr 1
    refine Finset.sum_congr rfl fun w hw => ?_
    unfold TruncatedSeriesCountingIdentities.lenW
    rw [dite_eq_right (Finset.disjoint_left.mp dc.disj hw)]
  have A1 : ∑ n ∈ rowsN i dc, qU (eON i).toNat (rowLen n) ≤ ∑ w ∈ dc.row, lenRow w := by
    rw [sum_rowsN]
    refine Finset.sum_le_sum fun v hv => ?_
    have hn : idx i dc v ∈ rowsN i dc := Finset.mem_image_of_mem _ hv
    have h2 := (hT4 _ hn).2
    rw [plOf_idx i dc (row_mem_plSet i dc hv)] at h2
    unfold qU
    rw [div_le_iff₀ hEpos]
    linarith
  have A2 : ∑ w ∈ Finset.univ.image (colIdx i dc),
      ((e'N i dc e' w : ℚ) + (jN i ρ π dc w : ℚ) * ((e'N i dc e' w : ℚ) + qU (eON i).toNat vδ) +
        2 * qU (eON i).toNat vδ + qU (eON i).toNat (h0d w)) ≤
      ∑ w ∈ dc.col, TruncatedSeriesCountingIdentities.lenW i ρ π dc lenRow e' w := by
    rw [sum_cols]
    refine Finset.sum_le_sum fun v hv => ?_
    have hpo := plOf_idx i dc (col_mem_plSet i dc hv)
    have hw : v ∈ placesOver D.host.E (D.nd.l i) := (dc.cover v).1 (Or.inr hv)
    have hjw : ∀ u (hu : u = v) (h : u ∈ placesOver D.host.E (D.nd.l i)),
        Br.jW D.loc D.nbr i u h ρ π = Br.jW D.loc D.nbr i v hw ρ π := by
      rintro u rfl h; rfl
    have hj : jN i ρ π dc (idx i dc v) = Br.jW D.loc D.nbr i v hw ρ π := by
      unfold jN
      rw [dite_eq_left (by rw [hpo]; exact hw)]
      exact hjw _ hpo _
    have he' : e'N i dc e' (idx i dc v) = e' v := by unfold e'N; rw [hpo]
    have hn : idx i dc v ∈ colsN i dc := Finset.mem_image_of_mem _ hv
    have hh : qU (eON i).toNat (h0d (idx i dc v)) ≤ Br.h0W i v ρ π := by
      rw [twist_invariants_unit_change]
      have h3 := hT3 _ hn
      rw [hpo] at h3
      exact qU_mono h3 (hF1 v hv).ne
    unfold TruncatedSeriesCountingIdentities.lenW
    rw [dite_eq_left hv]
    unfold Br.lenCol
    rw [hj, he', hvd]
    linarith
  have A3 : qU (eON i).toNat (sN i ρ π) = Br.sPi D.loc D.nbr i ρ π := (sPi_eq_qU i ρ π).symm
  have A4 : ∑ k ∈ Finset.Ioo 0 D.R.t, qU (eON i).toNat (ShaN i k) =
      ∑ k ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) k :=
    Finset.sum_congr rfl fun k hk => qU_ShaN i hk (hsha k hk)
  have A5 : ((padicValNat (D.nd.l i) (classNumber D.host.E) : ℕ) : ℚ) =
      (padicValNat (D.nd.l i) (Formalism.MainNotions.N.hE D.host) : ℚ) := rfl
  have A6 : ∑ n ∈ rowsN i dc, ((ReciprocityTheory.Gal.locDeg (plOf i dc n) : ℚ) + 2) * (cB : ℚ) =
      ∑ w ∈ dc.row, ((Formalism.MainNotions.N.locDeg D.host.E w : ℚ) + 2) * (cB : ℚ) := by
    rw [sum_rowsN]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [plOf_idx i dc (row_mem_plSet i dc hv)]
    rfl
  have A7 : 4 * ((Nn : ℚ) + D.R.t) * (((Finset.univ.image (colIdx i dc)).card : ℕ) + 1 : ℚ) *
      qU (eON i).toNat vδ = 4 * (D.R.nV : ℚ) * ((dc.col.card : ℚ) + 1) * D.nd.vdel i := by
    rw [card_cols, hvd, hN]
    unfold Ranks.nV
    push_cast
    ring
  have A8 : (D.R.t : ℚ) * (((Finset.univ.image (colIdx i dc)).card : ℕ) : ℚ) * qU (eON i).toNat (invariantsLengthSup i dc) ≤
      (D.R.t : ℚ) * (dc.col.card : ℚ) * h0 D.nd i dc.col := by
    rw [card_cols]
    exact mul_le_mul_of_nonneg_left (qU_H0N_le i dc) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have A9 : ∑ n ∈ qsN i dc, qU (eON i).toNat (IsDiscreteValuationRing.addVal (D.nd.O i) (zetaN i dc n - 1)) =
      ∑ v ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1}) := by
    rw [sum_qsN]
    refine Finset.sum_congr rfl fun v hv => ?_
    unfold zetaN
    rw [plOf_idx i dc (q_mem_plSet i dc hv), lenUnit_zeta]
  rw [A3, A4, A5, A6, A7, A9] at key
  rw [A0]
  linarith

end N9Main

section N9Cor

variable {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i)

open Formalism.MainNotions.N.Glob Formalism.BasicNotions.Loc

def SelmerLengthInequality (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ)
    (cB : ℕ) : Prop :=
  ∃ (rowLen h0d : ℕ → ℕ∞) (vδ : ℕ∞) (Nn : ℕ),
    vδ = eON i * ((∑ k ∈ Finset.Ioo 0 D.R.t, (D.nd.s0 i + padicValNat (D.nd.l i) k) : ℕ) : ℕ∞) ∧
    Nn = D.R.r ∧
    Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π) ≤
      ∑ w ∈ rowsN i dc, rowLen w +
        ∑ w ∈ Finset.univ.image (colIdx i dc), (eON i * (e'N i dc e' w : ℕ∞) +
          (jN i ρ π dc w : ℕ∞) * (eON i * (e'N i dc e' w : ℕ∞) + vδ) + 2 * vδ + h0d w) + sN i ρ π +
        ∑ e ∈ Finset.Ioo 0 D.R.t, ShaN i e +
        eON i * (padicValNat (D.nd.l i) (classNumber D.host.E) : ℕ∞) +
        (D.R.t : ℕ∞) * eON i * (cB : ℕ∞) * ∑ w ∈ rowsN i dc, ((ReciprocityTheory.Gal.locDeg (plOf i dc w) : ℕ∞) + 2) +
        4 * ((Nn : ℕ∞) + D.R.t) * (((Finset.univ.image (colIdx i dc)).card : ℕ∞) + 1) * vδ +
        (D.R.t : ℕ∞) * ((Finset.univ.image (colIdx i dc)).card : ℕ∞) * invariantsLengthSup i dc +
        (D.R.t : ℕ∞) * ∑ w ∈ qsN i dc, IsDiscreteValuationRing.addVal (D.nd.O i) (zetaN i dc w - 1) ∧
    TieRow i dc rowLen lenRow ∧ LeTwistInvariantsAtColumns i ρ π dc h0d

theorem theorem_of_display_inequality (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ)
    (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)
    (hD : D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → Br.sFin D.loc D.nbr i ρ π →
      (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
      SelmerLengthInequality i ρ π dc lenRow e' cB)
    (hF1 : FiniteTwistInvariants i ρ π dc) (hF2 : FiniteCharacterInvariants i dc) (hz : ZetaNe i) :
    TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB := by
  unfold TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem
  intro h0 h1 hZ hs hsha
  obtain ⟨rowLen, h0d, vδ, Nn, hvδ, hN, hd, hT4, hT3⟩ := hD h0 h1 hZ hs hsha
  exact selmer_length_inequality i ρ π dc lenRow e' cB rowLen h0d vδ Nn hvδ hN hd hT4 hT3 hF1 hF2 hz hs hsha

theorem zeta_ne_one_of_g5_extra (h : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) : ZetaNe i := by
  unfold ZetaNe TruncatedSeriesCountingIdentities.TameGeneratorConditions at *
  intro v hv
  have h2 := h v (Or.inr hv)
  tauto

theorem theorem_of_display (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ)
    (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)
    (hD : D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → Br.sFin D.loc D.nbr i ρ π →
      (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
      SelmerLengthInequality i ρ π dc lenRow e' cB)
    (hF1 : FiniteTwistInvariants i ρ π dc) (hF2 : FiniteCharacterInvariants i dc) (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) :
    TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB := theorem_of_display_inequality i ρ π dc lenRow e' cB hD hF1 hF2 (zeta_ne_one_of_g5_extra i h5x)

end N9Cor
end Formalism.MainNotions.N.K
end

section
open Classical
namespace Formalism.MainNotions.N.K.Sel
open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
section Gen
variable {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
  {M W : Type} [AddCommGroup M] [Module O M] [AddCommGroup W] [Module O W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousConstSMul O W]
  (ρM : Representation O G M) (ρW : Representation O G W) (φ : M ≃ₗ[O] W)
  (hφ : ∀ g m, φ (ρM g m) = ρW g (φ m))

include hφ

theorem symm_equiv (g : G) (w : W) : φ.symm (ρW g w) = ρM g (φ.symm w) := by
  apply φ.injective
  rw [hφ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

def psiZ : ReciprocityTheory.Gal.Z1 ρW →ₗ[O] coZ1s ρM where
  toFun f := ⟨fun g => φ.symm (f.1 g), fun g h => by
    show φ.symm (f.1 (g * h)) = φ.symm (f.1 g) + ρM g (φ.symm (f.1 h))
    rw [f.2.2 g h, map_add (f := _), symm_equiv ρM ρW φ hφ]⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

theorem psiZ_apply (f : ReciprocityTheory.Gal.Z1 ρW) (g : G) :
    (psiZ ρM ρW φ hφ f : G → M) g = φ.symm (f.1 g) := rfl

def psi : ReciprocityTheory.Gal.H1 ρW →ₗ[O] H1z ρM :=
  Submodule.mapQ _ _ (psiZ ρM ρW φ hφ) (by
    intro f hf
    obtain ⟨w, hw⟩ := (ReciprocityTheory.Gal.mem_coboundaries1 ρW _).1 hf
    refine ⟨φ.symm w, funext fun g => ?_⟩
    change ρM g (φ.symm w) - φ.symm w = φ.symm (f.1 g)
    rw [show f.1 g = ρW g w - w from hw g, map_sub, symm_equiv ρM ρW φ hφ])

theorem psi_mk (f : ReciprocityTheory.Gal.Z1 ρW) :
    psi ρM ρW φ hφ (Submodule.Quotient.mk f) = Submodule.Quotient.mk (psiZ ρM ρW φ hφ f) := rfl

theorem psi_injective : Function.Injective (psi ρM ρW φ hφ) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.mem_ker, psi_mk, Submodule.Quotient.mk_eq_zero] at hx
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  obtain ⟨m, hm⟩ := hx
  show f.1 ∈ ReciprocityTheory.Gal.B1 ρW
  rw [ReciprocityTheory.Gal.mem_coboundaries1]
  refine ⟨φ m, fun g => ?_⟩
  have h2 : φ.symm (f.1 g) = ρM g m - m := by
    first
    | exact (congrFun hm g).symm
  rw [← hφ, ← map_sub, ← h2, LinearEquiv.apply_symm_apply]

theorem lc_mem_range {x : H1z ρM} (hx : x ∈ lcH1 ρM) : ∃ y, psi ρM ρW φ hφ y = x := by
  obtain ⟨c, hc, rfl⟩ := hx
  have hc' : IsLocallyConstant (c : G → M) := hc
  have hcont : Continuous (fun g => φ ((c : G → M) g)) := (hc'.comp (⇑φ)).continuous
  have hcoc : ∀ g h, φ ((c : G → M) (g * h)) = φ ((c : G → M) g) + ρW g (φ ((c : G → M) h)) := by
    intro g h
    rw [c.2 g h, map_add (f := _), hφ]
  refine ⟨Submodule.Quotient.mk ⟨fun g => φ ((c : G → M) g), hcont, hcoc⟩, ?_⟩
  rw [psi_mk]
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk c
  congr 1
  apply Subtype.ext
  funext g
  simp only [psiZ_apply, LinearEquiv.symm_apply_apply]

theorem injTie_of {S : Submodule O (H1z ρM)} {S' : Submodule O (ReciprocityTheory.Gal.H1 ρW)}
    (hS : S ≤ lcH1 ρM) (h : ∀ y, psi ρM ρW φ hφ y ∈ S → y ∈ S') : InjTie S S' := by
  let T : Submodule O (ReciprocityTheory.Gal.H1 ρW) := S.comap (psi ρM ρW φ hφ)
  let gT : T →ₗ[O] S := (psi ρM ρW φ hφ).restrict (fun x hx => hx)
  have hg : Function.Bijective gT := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply psi_injective ρM ρW φ hφ
      exact congrArg Subtype.val hab
    · rintro ⟨x, hx⟩
      obtain ⟨y, hy⟩ := lc_mem_range ρM ρW φ hφ (hS hx)
      refine ⟨⟨y, ?_⟩, ?_⟩
      · show psi ρM ρW φ hφ y ∈ S
        rw [hy]
        exact hx
      · apply Subtype.ext
        exact hy
  let e := LinearEquiv.ofBijective gT hg
  refine ⟨(Submodule.inclusion (fun y hy => h y hy)).comp e.symm.toLinearMap, ?_⟩
  exact (Submodule.inclusion_injective (fun y hy => h y hy)).comp e.symm.injective

end Gen

end Formalism.MainNotions.N.K.Sel

namespace Formalism.MainNotions.N.K.Sel

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N
  Formalism.MainNotions.N.K Formalism.BasicNotions

section Unr

variable {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
  {M W : Type} [AddCommGroup M] [Module O M] [AddCommGroup W] [Module O W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousConstSMul O W]
  (ρM : Representation O G M) (ρW : Representation O G W) (φ : M ≃ₗ[O] W)
  (hφ : ∀ g m, φ (ρM g m) = ρW g (φ m))

theorem unr_tie {I Dg : Subgroup G} (y : ReciprocityTheory.Gal.H1 ρW)
    (h : Formalism.NG.resH1 ρM I (psi ρM ρW φ hφ y) = 0) :
    ReciprocityTheory.Gal.resH1 (ρW.comp Dg.subtype) (I.subgroupOf Dg).subtype continuous_subtype_val
      (ReciprocityTheory.Gal.resH1 ρW Dg.subtype continuous_subtype_val y) = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [psi_mk] at h
  change Submodule.Quotient.mk (restrictCocycles1 ρM I (psiZ ρM ρW φ hφ f)) = 0 at h
  rw [Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨m, hm⟩ := h
  show Submodule.Quotient.mk _ = 0
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, ReciprocityTheory.Gal.mem_coboundaries1]
  refine ⟨φ m, fun g => ?_⟩
  have hg' : φ.symm (f.1 ((g : Dg) : G)) = ρM ((g : Dg) : G) m - m := by
    have h1 := congrFun hm ⟨((g : Dg) : G), g.2⟩
    first
    | exact h1.symm
  show f.1 ((g : Dg) : G) = ρW ((g : Dg) : G) (φ m) - φ m
  rw [← hφ, ← map_sub, ← hg', LinearEquiv.apply_symm_apply]

end Unr

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i) {A T' : Type} [Ring A] [Algebra (D.nd.O i) A] [CommRing T'] [Algebra T' A]
  (M : Type) [AddCommGroup M] [Module A M] [Module (D.nd.O i) M] [SMulCommClass A (D.nd.O i) M]
  (r : GE D.nd →* A) (χ : GE D.nd →* T'ˣ)
  (φ : M ≃ₗ[D.nd.O i] KOG (D.nd.O i) D.R.r)
  (hφ : ∀ g m, φ (uRep (D.nd.O i) (M := M) r χ g m) = Br.WKO i ρ π g (φ m))

def BkAt (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) w)))) :
    Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (x : ReciprocityTheory.Gal.H1 (Br.WKO i ρ π)),
    Formalism.NG.resH1 (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) (idx i dc w))
              (psi (uRep (D.nd.O i) (M := M) r χ) (Br.WKO i ρ π) φ hφ x) ∈ F (idx i dc w) →
      ReciprocityTheory.Gal.resH1 (Br.WKO i ρ π) (decS D.nd w) continuous_subtype_val x ∈
        Br.bk D.loc D.nbr i w hw (WpO D.nd i ρ π)

theorem idx_mem_rows_cols {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    idx i dc w ∈ rowsN i dc ∪ Finset.univ.image (colIdx i dc) := by
  rcases (dc.cover w).mpr hw with h | h
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨w, h⟩, Finset.mem_univ _, rfl⟩)

theorem tieSel1_of
    (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) w))))
    (hBk : BkAt i dc ρ π M r χ φ hφ F) :
    TieSel1 i ρ π M r χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc) F (K.QS.Io i) := by
  refine injTie_of (uRep (D.nd.O i) (M := M) r χ) (Br.WKO i ρ π) φ hφ ?_ ?_
  · intro x hx
    exact (Submodule.mem_inf.mp (Submodule.mem_inf.mp hx).1).1
  · intro y hy
    obtain ⟨hy1, hloc⟩ := Submodule.mem_inf.mp hy
    have hunr := (Submodule.mem_inf.mp hy1).2
    unfold Br.selPi Br.selG Formalism.GaloisCohomology.SelAll
    refine (ReciprocityTheory.Gal.mem_Sel _ _ _ _ _).2 fun v => ?_
    unfold Formalism.GaloisCohomology.bkCond
    split_ifs with h1 h2
    · have hw : v ∈ placesOver D.host.E (D.nd.l i) := h1
      have hm := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hloc (idx i dc v))
        (idx_mem_rows_cols i dc hw)
      have hb := hBk v hw y hm
      unfold Br.LlG
      rw [dite_eq_left hw]
      exact hb
    · exact Submodule.mem_top
    · have hS : v ∉ D.nd.S i := fun h => h2 (Or.inl h)
      have hQ : v ∉ D.nd.Q i := fun h => h2 (Or.inr h)
      let vo : K.QS.Vo i := ⟨v, h1, hS, hQ⟩
      have hu := (Submodule.mem_iInf _).1 hunr vo
      exact unr_tie (uRep (D.nd.O i) (M := M) r χ) (Br.WKO i ρ π) φ hφ y hu

end Rec

end Formalism.MainNotions.N.K.Sel

namespace Formalism.MainNotions.N.K.Sel

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

section Row

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

def LenOlSelf : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    lenOl (Br.PD D.loc D.nbr i w hw) (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)) = eON i

def RowTie (rowLen : ℕ → ℕ∞) : Prop :=
  ∀ n ∈ rowsN i dc, ∀ (hw : plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) (b : ℚ),
    RowAt (Br.PD D.loc D.nbr i (plOf i dc n) hw) (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i (plOf i dc n) hw).LL))
        (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i (plOf i dc n) hw) (rDuO D.nd i r x)))
        ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i (plOf i dc n) hw) (T2O D.nd i ρ π)) b →
      rowLen n ≠ ⊤ ∧
        ((rowLen n).toNat : ℚ) ≤
          b * ((lenOl (Br.PD D.loc D.nbr i (plOf i dc n) hw)
            (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i (plOf i dc n) hw).LL))).toNat : ℚ)

end Row

end Formalism.MainNotions.N.K.Sel

namespace Formalism.MainNotions.N.K.Sel

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N
  Formalism.MainNotions.N.K Formalism.BasicNotions

section ResCompat

variable {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
  {M W : Type} [AddCommGroup M] [Module O M] [AddCommGroup W] [Module O W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousConstSMul O W]
  (ρM : Representation O G M) (ρW : Representation O G W) (φ : M ≃ₗ[O] W)
  (hφ : ∀ g m, φ (ρM g m) = ρW g (φ m))

theorem psi_res (Dg : Subgroup G) (x : ReciprocityTheory.Gal.H1 ρW) :
    psi (resRep ρM Dg) (ρW.comp Dg.subtype) φ (fun g m => hφ g m)
        (ReciprocityTheory.Gal.resH1 ρW Dg.subtype continuous_subtype_val x) =
      Formalism.NG.resH1 ρM Dg (psi ρM ρW φ hφ x) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  first
  | rfl

end ResCompat

section RecLoc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i) {A T' : Type} [Ring A] [Algebra (D.nd.O i) A] [CommRing T'] [Algebra T' A]
  (M : Type) [AddCommGroup M] [Module A M] [Module (D.nd.O i) M] [SMulCommClass A (D.nd.O i) M]
  (r : GE D.nd →* A) (χ : GE D.nd →* T'ˣ)
  (φ : M ≃ₗ[D.nd.O i] KOG (D.nd.O i) D.R.r)
  (hφ : ∀ g m, φ (uRep (D.nd.O i) (M := M) r χ g m) = Br.WKO i ρ π g (φ m))

def BkLoc (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) w)))) :
    Prop :=
  ∀ n ∈ rowsN i dc ∪ Finset.univ.image (colIdx i dc),
    ∀ (hw : plOf i dc n ∈ placesOver D.host.E (D.nd.l i))
      (y : ReciprocityTheory.Gal.H1 ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n)))),
      psi (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) n))
          ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n))) φ (fun g m => hφ g m) y ∈ F n →
        y ∈ Br.bk D.loc D.nbr i (plOf i dc n) hw (WpO D.nd i ρ π)

theorem bkAt_of_loc
    (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) w))))
    (h : BkLoc i dc ρ π M r χ φ hφ F) : BkAt i dc ρ π M r χ φ hφ F := by
  intro w hw x hx
  have hmem := idx_mem_rows_cols i dc hw
  have hwp : w ∈ plSet i dc := by
    unfold plSet
    rcases (dc.cover w).mpr hw with h' | h'
    · simp [h']
    · simp [h']
  have e : plOf i dc (idx i dc w) = w := plOf_idx i dc hwp
  generalize hn : idx i dc w = n at *
  subst e
  apply h n hmem hw
  first
  | (erw [psi_res]; exact hx)

end RecLoc

end Formalism.MainNotions.N.K.Sel

namespace Formalism.MainNotions.N.K.Sel

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

section LenUnit

theorem length_semilinear {R S N M : Type} [CommRing R] [CommRing S] [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module S M] (e : R ≃+* S) [RingHomInvPair (e : R →+* S) (e.symm : S →+* R)]
    [RingHomInvPair (e.symm : S →+* R) (e : R →+* S)] (f : N ≃ₛₗ[(e : R →+* S)] M) :
    Module.length R N = Module.length S M := by
  first
  | (unfold Module.length; congr 1; exact Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap f))

def quotSL {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) [RingHomInvPair (e : R →+* S) (e.symm : S →+* R)]
    [RingHomInvPair (e.symm : S →+* R) (e : R →+* S)] (x : R) :
    (R ⧸ Ideal.span {x}) ≃ₛₗ[(e : R →+* S)] (S ⧸ Ideal.span {e x}) where
  toFun := Ideal.quotientEquiv _ _ e (by rw [Ideal.map_span, Set.image_singleton]; rfl)
  invFun := (Ideal.quotientEquiv _ _ e (by rw [Ideal.map_span, Set.image_singleton]; rfl)).symm
  left_inv := RingEquiv.symm_apply_apply _
  right_inv := RingEquiv.apply_symm_apply _
  map_add' := map_add _
  map_smul' := by
    intro r y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.algebraMap_eq, map_mul]
    rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem lenOlSelf {D : D7} (i : D.nd.Loc) : LenOlSelf i := by
  intro w hw
  unfold lenOl eON
  rw [Br.PD_p]
  have h1 := RingHomInvPair.of_ringEquiv (D.nbr i w hw).eO
  have h2 := RingHomInvPair.symm ((D.nbr i w hw).eO : D.nd.O i →+* ↥(OL (D.nbr i w hw).LL))
    ((D.nbr i w hw).eO.symm : ↥(OL (D.nbr i w hw).LL) →+* D.nd.O i)
  have h := length_semilinear (D.nbr i w hw).eO (quotSL (D.nbr i w hw).eO ((D.nd.l i : ℕ) : D.nd.O i))
  rw [map_natCast] at h
  exact h.symm

end LenUnit
end Formalism.MainNotions.N.K.Sel
end

end
