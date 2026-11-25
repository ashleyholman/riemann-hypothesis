module

public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementS
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.CurveFormalFirstLevelHolds
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.HurwitzB
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.InverseEndoIntegralHolds
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Several

@[expose] public section

namespace Formalism.L2.Th1.G

alias curveNegNorm := _root_.Formalism.L2.Th1.G.curve_neg_norm_holds
alias weierstrass_biadditive_mod_equiv := _root_.Formalism.L2.Th1.G.curve_formal_first_level_holds
theorem curveRamified : CurveRamified := CurveRamified_of_shape _root_.Formalism.L2.Th1.G.ramified_shape_holds _root_.Formalism.L2.Th1.G.adjoint_unit_norm_holds _root_.Formalism.L2.Th1.G.inverse_endo_integral_holds

end Formalism.L2.Th1.G
