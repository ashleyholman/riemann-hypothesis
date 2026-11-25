module

public import Development.EtaleCohomology.CohomologicalPurity.FinLeafExc
public import Development.EtaleCohomology.CohomologicalPurity.LeafBdCut
public import Development.EtaleCohomology.CohomologicalPurity.LeafPBPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafHtpyMVPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafTailNervePf
public import Development.EtaleCohomology.CohomologicalPurity.LeafTailRep0OfVec
public import Development.EtaleCohomology.CohomologicalPurity.LeafHsRelPfSplit
public import Development.EtaleCohomology.CohomologicalPurity.LeafWCovPfB
public import Development.EtaleCohomology.CohomologicalPurity.LeafWEqvLPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafTauPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafWCechPf
public import Development.EtaleCohomology.CohomologicalPurity.FreePMapMk
public import Development.EtaleCohomology.CohomologicalPurity.IsPullbackOfApp
public import Development.EtaleCohomology.CohomologicalPurity.LeafActPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafAffEqvPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafConeCokPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafDblCokPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafDeltaPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafExactPf
import Development.EtaleCohomology.CohomologicalPurity.LeafExcSpPfMono
public import Development.EtaleCohomology.CohomologicalPurity.LeafFreeCovPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafGeoPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafGoodPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafHtpyOnePf
public import Development.EtaleCohomology.CohomologicalPurity.LeafHtpyZeroPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafImgHomPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafImgPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafMonoPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafNerveSplitPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafPBMapPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafPLocPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafRepPtPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafTauNatPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafTauOf
public import Development.EtaleCohomology.CohomologicalPurity.LeafTauTopPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafTauUPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafUnitsRepPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafWCechRec
public import Development.EtaleCohomology.CohomologicalPurity.LeafWGmPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafWLocPf
public import Development.EtaleCohomology.CohomologicalPurity.PresSheafify
public import Development.EtaleCohomology.CohomologicalPurity.WeightedVectorLaurentEvalHomTOne
public import Development.EtaleCohomology.KummerExtensions.EtaleWeightedBlowupExceptionalChartTorsorOfEquiv

@[expose] public section

namespace LateralTheory.Fin.LeafThom

theorem etale_boundary_monomorphism_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafMono :=
  LateralTheory.CohomologicalPurity.Bd.LeafMono_of

theorem etale_boundary_good_pair_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafGood :=
  LateralTheory.CohomologicalPurity.Bd.LeafGood_of

theorem etale_boundary_connecting_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafDelta :=
  LateralTheory.CohomologicalPurity.Bd.LeafDelta_of

theorem etale_boundary_exact_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafExact :=
  LateralTheory.CohomologicalPurity.Bd.LeafExact_of

theorem etale_boundary_generator_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafGen :=
  LateralTheory.CohomologicalPurity.Bd.LeafGen_of

theorem etale_boundary_image_hom_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafImgHom :=
  LateralTheory.CohomologicalPurity.Bd.LeafImgHom_of etale_boundary_generator_of_thom_isomorphism

theorem etale_boundary_image_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafImg :=
  LateralTheory.CohomologicalPurity.Bd.LeafImg_of etale_boundary_image_hom_of_thom_isomorphism

theorem etale_boundary_map_of_thom_isomorphism : LateralTheory.CohomologicalPurity.LeafBd :=
  LateralTheory.CohomologicalPurity.Bd.goal_of
    etale_boundary_monomorphism_of_thom_isomorphism
    LateralTheory.CohomologicalPurity.Bd.LeafPush_of
    etale_boundary_good_pair_of_thom_isomorphism
    etale_boundary_connecting_of_thom_isomorphism
    etale_boundary_exact_of_thom_isomorphism
    etale_boundary_image_of_thom_isomorphism

theorem etale_thom_pullback_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafPB :=
  LateralTheory.CohomologicalPurity.Thom.LeafPB_of
    _root_.LateralTheory.CohomologicalPurity.Thom.LeafGeo_of
    _root_.LateralTheory.CohomologicalPurity.Thom.LeafPBMap_of
    _root_.LateralTheory.CohomologicalPurity.Thom.LeafAffEqv_of

theorem etale_affine_line_homotopy_zero_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafHtpyZero :=
  LateralTheory.CohomologicalPurity.Thom.LeafHtpyZero_of

theorem etale_homotopy_mayer_vietoris_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafHtpyMV :=
  LateralTheory.CohomologicalPurity.Thom.LeafHtpyMV_of _root_.LateralTheory.CohomologicalPurity.FreeCovPf.LeafFreeCov_of

theorem etale_affine_homotopy_invariance_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafHtpy :=
  LateralTheory.CohomologicalPurity.Thom.LeafHtpy_of
    etale_affine_line_homotopy_zero_of_thom_isomorphism
    _root_.LateralTheory.CohomologicalPurity.Thom.LeafHtpyOne_of
    etale_homotopy_mayer_vietoris_of_thom_isomorphism

theorem etale_thom_tail_nerve_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafTailNerve :=
  LateralTheory.CohomologicalPurity.Thom.LeafTailNerve_of
    _root_.LateralTheory.CohomologicalPurity.Thom.LeafNerveSplit_of
    _root_.LateralTheory.CohomologicalPurity.Thom.LeafUnitsRep_of

theorem etale_thom_tail_representable_degree_zero_of_thom_isomorphism :
    LateralTheory.CohomologicalPurity.Thom.LeafTailRep0 :=
  LateralTheory.CohomologicalPurity.Thom.LeafTailRep0_of _root_.LateralTheory.CohomologicalPurity.Thom.LeafRepPt_of

theorem etale_thom_tail_representable_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafTailRep :=
  LateralTheory.CohomologicalPurity.Thom.LeafTailRep_of
    etale_thom_tail_nerve_of_thom_isomorphism
    etale_thom_tail_representable_degree_zero_of_thom_isomorphism

theorem etale_thom_tail_vanishing_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafTail :=
  LateralTheory.CohomologicalPurity.Thom.LeafTail_of
    etale_thom_tail_representable_of_thom_isomorphism
    etale_affine_homotopy_invariance_of_thom_isomorphism

theorem etale_thom_class_unit_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafTauU :=
  LateralTheory.CohomologicalPurity.Thom.LeafTauU_of _root_.LateralTheory.CohomologicalPurity.Thom.LeafGeo_of

theorem etale_thom_class_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafTau :=
  LateralTheory.CohomologicalPurity.Thom.ThomClassRestriction.LeafTau_of
    etale_boundary_map_of_thom_isomorphism
    _root_.LateralTheory.CohomologicalPurity.Thom.LeafGeo_of
    etale_thom_pullback_of_thom_isomorphism
    etale_thom_tail_vanishing_of_thom_isomorphism
    etale_thom_class_unit_of_thom_isomorphism
    _root_.LateralTheory.CohomologicalPurity.Thom.tauTop

theorem etale_thom_class_natural_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafTauNat :=
  LateralTheory.CohomologicalPurity.Thom.LeafTauNat_of _root_.LateralTheory.CohomologicalPurity.Thom.LeafGeo_of

theorem etale_mapping_cone_cokernel_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.ExcSp.LeafConeCok :=
  LateralTheory.CohomologicalPurity.Thom.ExcSp.leafConeCok_of

theorem etale_relative_homotopy_sequence_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.ExcSp.LeafHsRel :=
  LateralTheory.CohomologicalPurity.Thom.ExcSp.etale_relative_cohomology_iso_of_cone_and_double_cokernel_isos
    etale_mapping_cone_cokernel_of_thom_isomorphism
    _root_.LateralTheory.CohomologicalPurity.Thom.ExcSp.leafDblCok_of

theorem etale_thom_excision_specialization_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafExcSp :=
  LateralTheory.CohomologicalPurity.Thom.ExcSp.etaleSplitExcision_of_cokernel_relative
    _root_.LateralTheory.CohomologicalPurity.Thom.ExcSp.LeafCokIso_of
    etale_relative_homotopy_sequence_of_thom_isomorphism

theorem etale_chart_covering_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWCov :=
  LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWCov_of'
    _root_.LateralTheory.CohomologicalPurity.Thom.LeafGeo_of
    _root_.LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafPLoc_of
    _root_.LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWLoc_of

theorem etale_chart_cech_descent_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWCech :=
  LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWCech_of_data _root_.LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWData_of

theorem etale_chart_right_equivalence_of_thom_isomorphism :
    LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWEqvR :=
  LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWEqvR_of etale_chart_cech_descent_of_thom_isomorphism

theorem etale_chart_torsor_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWTors :=
  WeightedBlowupChartPointUnits.Cb.etale_weighted_blowup_exceptional_chart_torsor_of_equivalence
    etale_chart_right_equivalence_of_thom_isomorphism
    _root_.LateralTheory.CohomologicalPurity.Thom.LeafGeo_of
    etale_boundary_map_of_thom_isomorphism
    etale_thom_excision_specialization_of_thom_isomorphism
    LateralTheory.Fin.LeafExc.intersectionNumber_baseChange

theorem etale_chart_left_equivalence_of_thom_isomorphism :
    LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWEqvL :=
  LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWEqvL_of
    _root_.LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.LeafWGm_of
    etale_chart_torsor_of_thom_isomorphism

theorem etale_thom_chart_factorization_of_thom_isomorphism :
    LateralTheory.CohomologicalPurity.Thom.ExcP.LeafChartFact :=
  LateralTheory.CohomologicalPurity.Thom.ExcP.LeafChartFact_of
    _root_.LateralTheory.CohomologicalPurity.Thom.LeafGeo_of
    etale_chart_covering_of_thom_isomorphism
    etale_chart_right_equivalence_of_thom_isomorphism
    etale_chart_left_equivalence_of_thom_isomorphism

theorem etale_thom_excision_projective_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Thom.LeafExcP :=
  LateralTheory.CohomologicalPurity.Thom.excision_of_thom_chart_factorization
    etale_boundary_map_of_thom_isomorphism
    etale_thom_excision_specialization_of_thom_isomorphism
    etale_thom_chart_factorization_of_thom_isomorphism

theorem etale_thom_isomorphism_of_thom_isomorphism : LateralTheory.CohomologicalPurity.LeafThom :=
  LateralTheory.CohomologicalPurity.Thom.goal_of
    _root_.LateralTheory.CohomologicalPurity.Thom.LeafGeo_of
    _root_.LateralTheory.CohomologicalPurity.Thom.LeafAct_of
    etale_thom_class_of_thom_isomorphism
    etale_thom_class_natural_of_thom_isomorphism
    etale_thom_excision_projective_of_thom_isomorphism

theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafThom :=
  etale_thom_isomorphism_of_thom_isomorphism

end LateralTheory.Fin.LeafThom
