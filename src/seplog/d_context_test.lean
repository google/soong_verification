import seplog.c_program_test
import seplog.d_context

import utils

open Val open TypeDecl open cmd
open Binop open Relop open Expr open Unop

   /-
   - Abbreviate `to_pairmap_first_unique`
   -/
  def to_pm {α β: Type*} [decidable_eq α] (x: list (α × β)): pairmap α β
    := to_pairmap_first_unique x



/-
func (this *LL) cyclic(first bool, head *LL) (bool) {
  this_inst <- this;
  if first {
    head = this
  }

  if this.next == nil {
    return true
  } else if (this.next == head) {
    return false
  } else {
    return this.cyclic(false, head)
  }
}
-/
def cycsig: Sig := ⟨to_pm [("first", gBool), ("head", gPtr (gRef "LL"))],
                    to_pm [("res", gBool)], "this", tt⟩

def first: Var gBool               := ⟨"first"⟩
def this:  Expr (gPtr (gRef "LL")) := getvar ⟨"this"⟩
def this': Expr (gRef "LL")        := getvar ⟨"this_inst"⟩
def next:  Expr (gPtr (gRef "LL")) := this' ↠ "next"

/-
 - An INCORRECT implementation of `is_cyclic` because it fails to consider loops
 - that don't include the head of the list.
 -/
def cycprog: cmd :=
  (@declare (gRef "LL") ⟨"this_inst"⟩) ∣
  (@declare gBool ⟨"res"⟩) ∣
  (⟨"this_inst"⟩ ↩ this) ∣
  (ift (getvar first) (⟨"head"⟩ ⇐  this)) ∣
  (ifte (next ≃ (getvar ⟨"head"⟩))
    (⟨"res"⟩ ⇐ goTrue)
    (ifte (isNil next)
      (⟨"res"⟩ ⇐ goFalse)
      (@call "LL" (sum.inl next) "cyclic"
        [⟨_, goFalse⟩,⟨gPtr (gRef "LL"),(getvar ⟨"head"⟩)⟩] [⟨gBool, ⟨"res"⟩⟩])
    )
  )

def sumsig: Sig := ⟨∅, to_pm [("ret", gInt)], "this", tt⟩
def sumprog: cmd := skip


def LL: GoStructDecl "LL" := ⟨
  to_pm [("val", gInt), ("next", gPtr (gRef "LL"))],
  to_pm [("len", (sumsig, sumprog)), ("cyclic", (cycsig, cycprog))]⟩

def ll_decl:= list_to_decls [⟨_, LL⟩]
--------------------------------------------------------------------------------
/-
 - Class used to store the result of `ImageMutatorBegin` (until we implement
 - arrays)
 -/
def MutatorSet: GoStructDecl "MutatorSet" := ⟨to_pm [
    ("core", gPtr gBool),
    ("vendor_platform", gPtr gBool),
    ("vendor_board", gPtr gBool),
    ("product_platform", gPtr gBool),
    ("product_product", gPtr gBool),
    ("ramdisk", gPtr gBool),
    ("recovery", gPtr gBool)], ∅⟩

/-
 - Class stored as field of Module
 -/
def Vndkdep: GoStructDecl "Vndkdep" :=
    ⟨to_pm [("isVndk", gBool), ("isVndkExt", gBool),  ("isVndkSp", gBool)], ∅⟩

def imb_sig: Sig := ⟨∅, ∅, "m_ptr", tt⟩

def mptr: Var (gPtr $ gRef "Module") := ⟨"m_ptr"⟩
def m': Var (gRef "Module") := ⟨"m"⟩
def m: Expr (gRef "Module") := getvar m'

def vndkdep: Var (gPtr $ gRef "Vndkdep") := ⟨"vndkdep_ptr"⟩
def vndkdep_val: Var (gRef "Vndkdep") := ⟨"vndkdep"⟩
def err': Var (gPtr gErr) := ⟨"err"⟩
def err (msg: string): cmd := (m ↠ "PropertyError") ≪ (const $ pErr msg)
def va_nil := @isNil gBool (m ↠ "vendor_available")

def ms: TypeDecl := gRef "MutatorSet"
def ms_inst: Expr ms := getvar ⟨"ms"⟩
def update_cs (field: string) (var: string): cmd :=
              (ms_inst ↠ field) ≪ (@getvar gBool ⟨var⟩)

def imb : cmd :=
  -- Store the value of the module at mptr (we won't mutate until very end)
  (declare m') ∣ (declare vndkdep_val) ∣
  (m' ↩ getvar mptr) ∣ -- m below is defined as getvar m'

  -- For each of the possible variants, create a boolean flag to store result
  (⟨"vendor_platformVndkVersionVariantNeeded"⟩  :≃ goFalse) ∣
  (⟨"product_platformVndkVersionVariantNeeded"⟩ :≃ goFalse) ∣
  (⟨"vendor_boardVndkVersionVariantNeeded"⟩     :≃ goFalse) ∣
  (⟨"product_productVndkVersionVariantNeeded"⟩  :≃ goFalse) ∣
  (⟨"coreVariantNeeded"⟩                        :≃ goFalse) ∣
  (⟨"ramdiskVariantNeeded"⟩                     :≃ goFalse) ∣
  (⟨"recoveryVariantNeeded"⟩                    :≃ goFalse) ∣


  (@Var.mk gBool "vendorSpecific" :≃ ((m ↠ "SoCSpecific")
                                      ⋁ (m ↠ "DeviceSpecific"))) ∣

  (@Var.mk gBool "productSpecific" :≃ (m ↠ "ProductSpecific")) ∣


  (ifte (va_nil⋀ getvar ⟨"vendorSpecific"⟩)
    (err $ "vendor_available doesn't make sense at the same time as "
           ++ "`vendor: true`, `proprietary: true`, or `device_specific:true")
    skip ) ∣

  (vndkdep :≃ (m ↠ "vndkdep")) ∣  -- variable holding a pointer


  (ift (¡ (isNil (getvar vndkdep)))
    ((vndkdep_val ↩ getvar vndkdep) ∣
      (ifte (getvar vndkdep_val ↠ "isVndk")
        (ifte (getvar ⟨"vendorSpecific"⟩ ⋁  getvar ⟨"productSpecific"⟩)
          (ifte (¡(getvar vndkdep_val ↠ "isVndkExt"))
            (err "vvndk must set `extends: \"...\"` to vndk extension ")
            (ift (¡ va_nil)
              (err $ "Vendor_available must not set at the same time as `vndk: "
                     ++ "{extends: \"...\"}`")
            )
          )
          (ift (getvar vndkdep_val ↠ "isVndkExt")
            (err $ "vndk: must set `vendor: true` or `product_specific: true` "
                   ++ "to set `extends: %q`")
          ) ∣
          (ift va_nil
            (err $ "vndk: vendor_available must be set to either true or false "
                   ++ "when `vndk: {enabled: true}`")
          )
        )
        (ift (getvar vndkdep_val ↠ "isVndkSp")
          (err $ "vndk: must set `enabled: true` to set "
                ++ "`support_system_process: true`")
        ) ∣
        (ift (getvar vndkdep_val ↠ "isVndkExt")
          (err $ "vndk: must set `enabled: true` to set `extends: %q`")
        )
      )
    )
  ) ∣

  /- Then there is some logic with versioning, but we assume we are using
   - current version. This means `isSnapshotPrebuild` is false and
   - boardVndkVersion/Sdk_version are not ""
   -/
  ifs [
    (m ↠ "llndkStubDecorator",
      -- LL-NDK stubs only exist in the vendor and product variants,
      -- since the real libraries will be used in the core variant.
      ((⟨"vendor_platformVndkVersionVariantNeeded"⟩  ⇐ goTrue) ∣
       (⟨"vendor_boardVndkVersionVariantNeeded"⟩     ⇐ goTrue) ∣
       (⟨"product_platformVndkVersionVariantNeeded"⟩ ⇐ goTrue) ∣
       (⟨"product_productVndkVersionVariantNeeded"⟩  ⇐ goTrue))
    ),
    (m ↠ "llndkHeadersDecorator",
      --... and LL-NDK headers as well TODO learn why this is a separate branch
      ((⟨"vendor_platformVndkVersionVariantNeeded"⟩  ⇐ goTrue) ∣
       (⟨"vendor_boardVndkVersionVariantNeeded"⟩     ⇐ goTrue) ∣
       (⟨"product_platformVndkVersionVariantNeeded"⟩ ⇐ goTrue) ∣
       (⟨"product_productVndkVersionVariantNeeded"⟩  ⇐ goTrue))
    ),
    (m ↠ "HasVendorVariant" ⋀ (¡ (getvar vndkdep_val ↠ "isVndkExt")),
      (
       (⟨"coreVariantNeeded"⟩ ⇐ goTrue) ∣

       (ifte (m ↠ "moduleDirIsVendorPath")
        (⟨"vendor_boardVndkVersionVariantNeeded"⟩     ⇐ goTrue)
        (⟨"vendor_platformVndkVersionVariantNeeded"⟩  ⇐ goTrue)
       ) ∣

       (⟨"product_platformVndkVersionVariantNeeded"⟩ ⇐ goTrue) ∣

       (ift (¡(m ↠ "isVndk"))
              (⟨"product_productVndkVersionVariantNeeded"⟩  ⇐ goTrue))
       )
    )

    ] (⟨"coreVariantNeeded"⟩ ⇐ goTrue) ∣-- otherwise

  (ifte ((¡(isEmpty (m ↠ "boardVndkVersion")) ⋀
         (¡(isEmpty (m ↠ "productVndkVersion")))))

    (ift (getvar ⟨"coreVariantNeeded"⟩ ⋀ isEmpty (m ↠ "boardSdkVersion"))
      -- Module has "product_specific: true" that does not create core variant.
      ((⟨"coreVariantNeeded"⟩                        ⇐ goFalse)) ∣
       (⟨"product_productVndkVersionVariantNeeded"⟩  ⇐ goTrue)
      )

    /- Unless PRODUCT_PRODUCT_VNDK_VERSION is set, product partition has no
		 - restriction to use system libs. No product variants defined in this case.
     -/
    ((⟨"product_platformVndkVersionVariantNeeded"⟩ ⇐ goFalse) ∣
     (⟨"product_productVndkVersionVariantNeeded"⟩  ⇐ goFalse)
    )
  ) ∣

  ift (m ↠ "Ramdisk_available") (⟨"ramdiskVariantNeeded"⟩ ⇐ goTrue) ∣

  ift (m ↠ "installInRamdisk")
    ((⟨"ramdiskVariantNeeded"⟩ ⇐ goTrue) ∣
     (⟨"coreVariantNeeded"⟩ ⇐ goTrue)
    ) ∣

  ift (m ↠ "Recovery_available") (⟨"recoveryVariantNeeded"⟩ ⇐ goTrue) ∣

  ift (m ↠ "installInRecovery")
    ((⟨"recoveryVariantNeeded"⟩ ⇐ goTrue) ∣
     (⟨"coreVariantNeeded"⟩ ⇐ goTrue)
    ) ∣


  (@new (gRef "MutatorSet") ⟨"ms"⟩) ∣ -- Create a MutatorSet object

  update_cs "core" "coreVariantNeeded" ∣
  update_cs "vendor_platform" "vendor_platformVndkVersionVariantNeeded" ∣
  update_cs "vendor_board" "vendor_boardVndkVersionVariantNeeded" ∣
  update_cs "product_product" "product_productVndkVersionVariantNeeded" ∣
  update_cs "product_platform" "product_platformVndkVersionVariantNeeded" ∣
  update_cs "ramdisk" "ramdiskVariantNeeded" ∣
  update_cs "recovery" "recoveryVariantNeeded" ∣

  (@mutation ms (m ↠ "ExtraVariants") ms_inst)


/-
 - Rather than call `imb` as a method of a `Module` object, we can treat it as
 - a program that has a hard-coded constant callee.
 -/
def imb_const(x: Val (gRef "Module")): cmd :=
   (m' ⇐ const x) ∣ imb

def Mod: GoStructDecl "Module" := ⟨
    to_pm [("name",                 gStr),
          ("PropertyError",         gPtr gErr),
          ("ExtraVariants",         gPtr (gRef "MutatorSet")),
          ("SoCSpecific",           gBool),
          ("vendor_available",      gPtr gBool),
          ("DeviceSpecific",        gBool),
          ("ProductSpecific",       gBool),
          ("vndkdep",               gPtr $ gRef "Vndkdep"),
          ("llndkHeadersDecorator", gBool),
          ("llndkStubDecorator",    gBool),
          ("moduleDirIsVendorPath", gBool),
          ("isVndk",                gBool),
          ("Ramdisk_available",     gBool),
          ("installInRamdisk",      gBool),
          ("Recovery_available",    gBool),
          ("installInRecovery",     gBool),
          ("HasVendorVariant",      gBool),
          ("boardVndkVersion",      gStr),
          ("productVndkVersion",    gStr),
          ("boardSdkVersion",       gStr),
          ("PropertyError",         gPtr gErr)
          ],
    to_pm [("ImageMutatorBegin", (imb_sig, imb ))]⟩

def imb_decls: Decls := list_to_decls [⟨_, Vndkdep⟩, ⟨_, MutatorSet⟩, ⟨_, Mod⟩]

run_cmd test (default gInt ∅)               $ some (pInt 0)
run_cmd test (default gStr imb_decls)       $ some (pStr "")
run_cmd test (default (gRef "a") imb_decls) none

run_cmd test (imb_decls.structs.lookup "Vndkdep") $ some ⟨(), Vndkdep⟩

/-
 - This is what we'd expect the default `GoStruct` should be based on the
 - `GoStructDecl` in `imb_decls`
 -/
def default_vndkdep := list_to_struct "Vndkdep" [
  ("isVndk",    ⟨_, pBool ff⟩),
  ("isVndkExt", ⟨_, pBool ff⟩),
  ("isVndkSp",  ⟨_, pBool ff⟩)]

run_cmd test (default (gRef "Vndkdep") imb_decls)
              (some $ default_vndkdep)

