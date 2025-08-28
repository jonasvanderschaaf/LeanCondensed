/-
Copyright (c) 2025 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf
-/
import Mathlib

open CategoryTheory

variable {C : Type*} [Category C] {D : Type*} [Category D] {F G : C ⥤ D}

lemma epi_of_rightEpi {f g : Arrow C} (π : f ⟶ g) [Epi f.hom] [Epi π.right] : Epi g.hom :=
  have : Epi (π.left ≫ g.hom) := by
    rw [←Functor.id_map π.left, π.w, Functor.id_map]
    infer_instance
  epi_of_epi (π.left) _

lemma epi_ofRetract {f g : Arrow C} (r : Retract g f) [Epi f.hom] : Epi g.hom :=
  epi_of_rightEpi r.r

lemma preservesEpi_ofEpi {f : F ⟶ G} (hf : ∀ X, Epi (f.app X)) [F.PreservesEpimorphisms] :
    G.PreservesEpimorphisms where
  preserves {X Y} π hπ :=
    have : Epi (f.app X ≫ G.map π) := by
      rw [←f.naturality π]
      infer_instance
    epi_of_epi (f.app X) _

lemma preservesEpi_ofRetract (r : Retract G F) [F.PreservesEpimorphisms] :
  G.PreservesEpimorphisms := preservesEpi_ofEpi
    (fun _ ↦ (r.map ((evaluation _ _).obj _)).splitEpi.epi)
