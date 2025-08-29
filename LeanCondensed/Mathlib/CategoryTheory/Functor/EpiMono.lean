/-
Copyright (c) 2025 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf
-/
import Mathlib

open CategoryTheory

variable {C : Type*} [Category C] {D : Type*} [Category D] {F G : C ⥤ D}
  [F.PreservesEpimorphisms]

lemma preservesEpi_ofEpi {f : F ⟶ G} (hf : ∀ X, Epi (f.app X)) : G.PreservesEpimorphisms
    where
  preserves {X Y} π hπ :=
    have : Epi (f.app X ≫ G.map π) := by
      rw [←f.naturality π]
      infer_instance
    epi_of_epi (f.app X) _

lemma preservesEpi_ofRetract (r : Retract G F) : G.PreservesEpimorphisms :=
  preservesEpi_ofEpi
    (fun _ ↦ (r.map ((evaluation _ _).obj _)).splitEpi.epi)
