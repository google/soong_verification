import data.finset.basic
import data.fintype.basic

/-
High-level model of Soong build system (very incomplete)

 Concrete examples of libraries:

 /system/bin/cameraserver
 - soong world: no options specified (meaning, 'local to system')

 /vendor/bin/vndservicemanager
 - soong world: "vendor: true" (meaning, 'local to vendor')

 libgui
 - soong world: "vendor_available: false, vndk: { enabled: true, },"
 - "vndk-private"

 libcamerahelper
 - soong world: "vendor_available: true, vndk: { enabled: true, },"
 - soong world: "libcamerahelper loads libgui" -- not important to model, this
                actually the relationship between vndk and vndk-private
 - "vndk"

 libbinder_ndk
 - soong world: "vendor_available: true, isLlNdk() true"
 - ll-ndk
 -/

--------------------------------------------------------------------------------
/-
 - Core data structures of Soong model
 -/

/-
 - Different kinds of libraries which have regular behavior in some sense
 - This does not correspond to any particular abstraction in the codebase but
 - is very useful for clarifying a mental model of how things work (lots of
 - behavior can be defined purely in virtue of what library classes a library
 - inhabits, without having to look at details of the library itself).
 -/
@[derive decidable_eq]
inductive Library_class
 | system_local: Library_class
 | system_ext: Library_class
 | vendor_local: Library_class
 | llndk: Library_class
 | vndk: Library_class
 | vndk_sp: Library_class
 | vndk_ext: Library_class
 | vndk_private: Library_class
 | product: Library_class
 | recovery: Library_class

open Library_class

/-
 - Being assigned some subset of these variants is a property of a given library
 - Which are assigned ends up dictating the build environment to a large degree.
 -/
@[derive decidable_eq]
inductive Variant
 | core: Variant
 | vendor_platform : Variant
 | product_platform : Variant
 | product_product : Variant
 | ramdisk : Variant
 | recovery : Variant

/-
 - Specified by a user in a Soong input file.
 -/
@[derive decidable_eq]
structure Library :=
 (name: string)

 (vendor_available: option bool)

 (vendor: option bool)
 -- declared as a VNDK or VNDK-SP module. The vendor variant
    -- will be installed in /system instead of /vendor partition.
    -- if true, then vendor_available must be explicitly set to either ⊤ or ⊥
 (vndk_enabled: option bool)
 -- declared as a VNDK-SP module, which is a subset of VNDK (need vndk_enabled).
    -- All these modules are allowed to link to VNDK-SP or LL-NDK
    -- modules only. Other dependency will cause link-type errors.
    -- none/false means lib is VNDK-core
    -- can link to other VNDK-core ,VNDK-SP or LL-NDK modules only.
    -- Warning: sometimes erroneously referred to as support_same_process
 (vndk_support_system_process: option bool)
 -- Whether m.linker(*llndkStubDecorator) returns true or not
 -- Assume that llndkHeadersDecorator has same value
 -- Modeled as a boolean field for simplicity
 (llndk_stub: bool)

 (device_specific: bool)
 (product_specific: bool)
 (is_vndk: bool)
 (is_vndkext: bool)
 -- Dependencies on other libraries by name
 (deps: finset string)

/-
 - Based on Jiyong's summary
 - The "none" corresponds to the very first check of ImageMutatorBegin, where
 - it fails because having both of these options set doesn't make sense
 - TODO consider all four booleans together,
 -   vndk-private is when vendor_available is false but vndk_enabled is true
 -   vndk_sp_private is the same as above but also has
 -     vndk_support_system_process true
 -/
def assign_library_classes (lib: Library): option (finset Library_class) :=
 (option.lift_or_get finset.has_union.1)

 (match lib.vendor, lib.vendor_available  with
  | (some _),      (some _)  := none
  | (some vendor), _         := some [vendor_local].to_finset
  | _,             (some tt) := some [vendor_local, system_local].to_finset
  | _,             (some ff) := some [system_local].to_finset -- TODO CHECK THIS
  | none,          none      := some [system_local].to_finset
  end)
  $  (option.lift_or_get finset.has_union.1)

  (match lib.vndk_enabled, lib.vndk_support_system_process with
    | (some tt), (some tt) := some [vndk_sp].to_finset
    | (some tt), _         := some [vndk].to_finset
    | _,         (some _)  := none
    | _,          _        := some ∅
   end)

  (some $ if lib.llndk_stub then [llndk].to_finset else ∅)

/-
 - Based on the implemenation at ~3122 of cc.go
 - Relies on assign_library_classes
 -/
 open Variant
 def libaryclass_to_variants: Library_class → finset Variant
 | system_local:= [core].to_finset
 | system_ext:= [core].to_finset
 | vendor_local:= [].to_finset -- aka vendorSpecific (ignore kernelHeadersDecorator) and ignore vendor board (it's experimental) only look at line 255
 | llndk:= [].to_finset -- variants from lines 187-197
 | vndk:= [core].to_finset -- AND whatever is in vendor_local
 | vndk_sp:= [].to_finset -- SAME as vndk
 | vndk_ext:= [].to_finset -- same as vendor_local
 | vndk_private:= [].to_finset -- same as vendor_local
 | product:= [core].to_finset
 | recovery:= [Variant.recovery].to_finset




/-
 - Map over and union
 - That we can do this is the justification of library_class' existance.
 - All members of a library class share variants.
 -/
def libary_to_variant (libc: Library): option (finset Variant):=
  assign_library_classes libc >>= λ lcs, some $
    (libclasses.1.map library_class_to_variants).fold (∪) ∅

--------------------------------------------------------------------------------
/-
 - Transitive relationship of reachability in a graph
 -/
inductive depends: finset Library → Library → Library → Prop
 | edge: ∀ (ctx: finset Library) (src tar: Library),
    src ∈ ctx → tar ∈ ctx
        → tar.name ∈ src.deps
            → depends ctx src tar
 | trans: ∀ (ctx: finset Library) (src mid tar: Library),
    src ∈ ctx → tar ∈ ctx
        → depends ctx src mid
            → depends ctx mid tar
                → depends ctx src tar


--------------------------------------------------------------------------------
/-
 - Concrete library examples
 -/
-- def cameraserver: Library := ⟨"cameraserver", none, none, none, ∅⟩
-- def libcamerahelper: Library := ⟨"libcamerahelper", some tt, none, none, ∅⟩
-- def vndservicemanager: Library := ⟨"vndservicemanager", ff, none, none, ∅⟩
-- def libgui: Library := ⟨"libgui", some ff, none, none, ∅⟩
-- def libutils: Library := ⟨"libutils", some tt, none, none, ∅⟩
--------------------------------------------------------------------------------
/-
 - Proofs about the model
 -/

theorem assign_library_classes_nonempty:
  forall lib: Library, ¬ (assign_library_classes lib) = some ∅
 := sorry

-- theorem double_loadable:
--   forall llndklib vndklib: LibraryWithClass, llndklib <= vndklib
--     → vndklib.double_loadable
--  := sorry
