import data.finset.basic
import data.fintype.basic
import seplog.c_program

/-

 1). module with properties like vendor_available (soong object)
 2). imageMutator
 3). structure Module with partition, and library class (vndk, ll-ndk, etc..)
 4). checkDoubleLoadable (need definition of this)

 a). every library will be installed to >= 1 library classes
 b). partitions: system.img, vendor.img, product.img, system_ext.img,
                 recovery.img
 c). library class: local (per partition), vndk, vndk-private, vndk-sp,
                    vndk-sp-private, ll-ndk, ll-ndk-private, sphal
 d). every library class will be installed on a certain partition
 e). for every library class, we have a '-private' library class. You could
     consider the '-private' class of vndk-private to be itself.
 f). a library class is able to load from another class, either directly or in
     another namespace

- if X library class relates to vndk, then X library class relates to vndk-sp
  (vndk-sp is a subset of vndk)

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
 - soong world: "vendor_availabel: true, isLlNdk() true"
 - ll-ndk

 class rules:
 - any 'local' binary can load another local binary
 - local vendor binary can load a vndk (and therefore a vndk-sp library)
 - vendor can load ll-ndk, and when it loads ll-ndk, it'll be in another
    namespace

Examples of what happens:
- notice libcamerahelper loads libgui
- cameraserver can load libgui
- cameraserver can load libcamerahelper
- vndservicemanager can not load libgui! (because vndk-private)
- vndservicemanager can load libcamerahelper (which loads libgui)
- vndservicemanager can load libbinder_ndk (which loads libutils) (all in
    another namespace)
- vndservicemanager can load libutils directly (in the same "default" namespace
    as vndservicemanager)
- libutils must be marked double_loadable

- if we have ll-ndk library which loads a vndk library, then that vndk library
    must be double_loadable


-- TODO: examples of vendor/vendor_available
- vendor: false/nil -> local system
- vendor: true -> local vendor
- vendor_available: we also go to local vendor
- system_ext_specific: true -> local system_ext
- system_ext_specific: true and vendor_available: true -> local vendor +
                        local system_ext
- vendor: false and vendor_available: true -> local vendor + local system
- vendor_available: false, vndk { enabled: true } -> vndk-private which is
        located on vendor image

-- linkerconfig definitions of relationships between classes (Library_class)
system -> [sphal, vndk]

definitions of these classes


First property to prove: the mapping function never returns an empty list
(everything maps to SOME partition)

 -/

--------------------------------------------------------------------------------
/-
 - Core data structures of Soong model
 -/


/- e.g. vndk (installed on system),
     vndk-private, vndk-sp, vndk-sp-private, local "default" system,
     local "default" <partition> (installed on <partition>)


    Vendor_local refers to all non-vndk / non-vndk_sp / non-vndk_private
        vendor libaries (i.e. installed to the vendor.image)
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
 - Platform and board versions are the same when version = current
 -/
@[derive decidable_eq]
inductive Variant
 | core: Variant
 | vendor_platform : Variant
 --| vendor_board : Variant
 | product_platform : Variant
 | product_product : Variant
 | ramdisk : Variant
 | recovery : Variant

/-
will have these "VendorProperties": http://cs/android/build/soong/cc/
    cc.go?l=284&rcl=96d4f4550ae0ec4414d5aa3991a796e653728a3e
and thse VNDK Properties: http://cs/android/build/soong/cc/
    vndk.go?l=58&rcl=a73f4ae43756fea07e7f422875da4c0040a0b8f6
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

/- Properties of libraries used in ImageMutator but can be ignored for present
   purposes

/*
    VERSION RELATED CODE - IGNORE ANYTHING TOUCHING THIS
                          (doesn't show up on normal builds)

    because boardVndkVersion will be platformVndkVersion rather than ""
    - DeviceConfig().PlatformVndkVersion()
    - DeviceConfig().VndkVersion()
    - mctx.DeviceConfig().ProductVndkVersion()
    - .Properties.Sdk_version
    - .isSnapshotPrebuilt()
    - mctx.ModuleDir()
    - HasVendorVariant
    - .linker.(interface {version() string})
    - linker.(*kernelHeadersDecorator);
*/

/* Also not relevant
    Properties.Ramdisk_available
    ModuleBase.InstallInRamdisk()
    Properties.Recovery_available
    InstallInRecovery()
*/

Properties.ExtraVariants (this is the result?)

-/

/-
 - Unclear how this is different from Library_class
 -/
structure LibraryWithClass :=
 (name: string) (libclass: Library_class)

/-
 - Based on Jiyong's summary
 - The "none" corresponds to the very first check of ImageMutatorBegin, where
 - it fails because having both of these options set doesn't make sense
 - TODO consider all four booleans together,
 -   vndk-private is when vendor_available is false but vndk_enabled is true
 -   vndk_sp_private is the same as above but also has vndk_support_system_process true
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
 - Code lines refer to http://cs/android/build/soong/cc/image.go?rcl=74d255698bf0e38572aa104872ba8f7a46a6da59
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
  assign_library_classes libc >>= λ lcs, some
    (if )

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

--------------------------------------------------------------------------------
/-
 - Proofs about Go code in relation to the model
 -/

-- These things are defined elsewhere, use dummies for now

/-
 - For an cmd corresponding to a function call with a single input/output,
 - a proof that the function called on the input yields the output
 - The output value is optional, where none value signals that the program is
 - expected to FAIL
 -/
def check_input_output: Π(α β: TypeDecl),
    cmd → Val α → option (Val β) → Prop := sorry

/-
 - Formal Go model of the program
 -/
def image_mutator: cmd := sorry

open TypeDecl
/-
 - Trivial mappings into Go objects from the formal model
 -/
def Lib_to_Go: Library → Val (gRef "Module") := sorry


def Classlist_to_Go: finset Library_class → Val (gRef  "ListModuleClass")
  := sorry

/-
 - We expect the Go model to function identically to the specification above
 -/
open TypeDecl

theorem image_mutator_meets_specification:
    ∀ (lib: Library),
        check_input_output (gRef "Module") (gRef "ListModuleClass")
            image_mutator
            (Lib_to_Go lib)
            ((option.map Classlist_to_Go) (assign_library_classes lib))
    := sorry

