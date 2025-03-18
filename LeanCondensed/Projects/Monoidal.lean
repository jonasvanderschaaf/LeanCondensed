import Mathlib.Topology.Category.LightProfinite.Sequence
import LeanCondensed.Mathlib.Condensed.Light.Limits
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection

universe u v

noncomputable section

open CategoryTheory LightProfinite OnePoint Limits LightCondensed MonoidalCategory MonoidalClosed

attribute [local instance] CategoryTheory.HasForget.instFunLike ModuleCat.instMonoidalClosed Sheaf.monoidalCategory

variable (R : Type u) [CommRing R] -- might need some more assumptions

instance : ((coherentTopology LightProfinite).W (A := ModuleCat R)).IsMonoidal :=
  GrothendieckTopology.W.monoidal

/- This is the monoidal structure on localized categories. -/
instance : MonoidalCategory (LightCondMod.{u} R) := CategoryTheory.Sheaf.monoidalCategory _ _

instance : MonoidalPreadditive (LightCondMod.{u} R) := sorry

instance : MonoidalClosed (LightProfinite.{u}ᵒᵖ ⥤ ModuleCat.{u} R) :=
  haveI : ∀ (F₁ F₂ : LightProfinite.{u}ᵒᵖ ⥤ (ModuleCat.{u}) R), Enriched.FunctorCategory.HasFunctorEnrichedHom (ModuleCat.{u} R) F₁ F₂ := inferInstance
  FunctorCategory.monoidalClosed

/- Constructed using Day's reflection theorem. -/
instance : MonoidalClosed (LightCondMod.{u} R) :=
  haveI : HasWeakSheafify ((coherentTopology LightProfinite.{u})) (ModuleCat R) := inferInstance
  haveI : (presheafToSheaf (coherentTopology LightProfinite) (ModuleCat R)).Monoidal := inferInstance
  haveI : (sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat R)).Faithful := (fullyFaithfulSheafToPresheaf _ _).faithful
  haveI :  (sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat R)).Full := (fullyFaithfulSheafToPresheaf _ _).full
  Monoidal.Reflective.monoidalClosed (sheafificationAdjunction _ _)
