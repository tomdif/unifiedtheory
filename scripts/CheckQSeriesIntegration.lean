/- Run after the focused build:
   lake build UnifiedTheory.LayerA.WatsonSeriesBridge UnifiedTheory.LayerA.MacMahonBridge
   lake env lean scripts/CheckQSeriesIntegration.lean

All printed dependencies should be a subset of
`propext`, `Classical.choice`, and `Quot.sound`.
-/
import UnifiedTheory.LayerA.WatsonSeriesBridge
import UnifiedTheory.LayerA.MacMahonBridge

open UnifiedTheory.QSeries
open UnifiedTheory.LayerA

#check WatsonSeriesBridge.chi0_R1
#check WatsonSeriesBridge.chi0_R1_coeff
#check WatsonSeriesBridge.chi0_even_argument_elimination
#check coeff_weightedEuler_computable
#check MacMahonBridge.mac3_eq_product_coeff

#print axioms Watson.chi0_R1_watson
#print axioms Watson.watson_2_0
#print axioms Watson.watson_3_0
#print axioms WatsonSeriesBridge.chi0_R1_coeff
#print axioms WatsonSeriesBridge.chi0_even_argument_elimination
#print axioms WatsonSeriesBridge.distinct_times_unrestricted_denominator
#print axioms WatsonSeriesBridge.distinct_eq_odd_partition_product
#print axioms eulerFactor_cancels
#print axioms coeff_weightedEulerPartial_stable
#print axioms coeff_weightedEuler_computable
#print axioms coeff_weightedEuler_nonneg
#print axioms MacMahonBridge.mac3_eq_product_coeff
#print axioms MacMahonBridge.mac_eq_solid_through_5
#print axioms MacMahonBridge.mac3_six
#print axioms MacMahonBridge.mac3_seven
#print axioms MacMahonBridge.first_discrepancy

-- Exact coefficients of the infinite product, checked by Lean's kernel.
example : PowerSeries.coeff 6 macMahonProduct = 141 := by
  rw [MacMahonBridge.mac3_eq_product_coeff, MacMahonBridge.mac3_six]
  norm_num

example : PowerSeries.coeff 7 macMahonProduct = 310 := by
  rw [MacMahonBridge.mac3_eq_product_coeff, MacMahonBridge.mac3_seven]
  norm_num

-- The general stabilization theorem applies to arbitrary further truncations.
example (N : ℕ) (hN : 6 ≤ N) :
    PowerSeries.coeff 6 (weightedEulerPartial macMahonMultiplicity N) = 141 := by
  rw [← coeff_weightedEuler macMahonMultiplicity hN]
  change PowerSeries.coeff 6 macMahonProduct = 141
  rw [MacMahonBridge.mac3_eq_product_coeff, MacMahonBridge.mac3_six]
  norm_num
