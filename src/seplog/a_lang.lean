import data.finset.basic
import data.finset.sort
import data.finset.fold
import data.finmap

/-
 - Model of Golang.
 -/

section language_types
  /-
   - This is a type whose members are specifications of Go types
   - A member of this type is not an *instance* of a Go type
   - E.g. gInt takes no arguments.
   -/
  @[derive decidable_eq]
  inductive TypeDecl: Type
   | gInt:  TypeDecl
   | gStr:  TypeDecl
   | gErr:  TypeDecl
   | gBool: TypeDecl
   | gPtr:  TypeDecl → TypeDecl
   | gArr:  ℕ → TypeDecl → TypeDecl
   | gRef:  string → TypeDecl  -- refer to something globally defined by name

  instance: inhabited TypeDecl := ⟨TypeDecl.gInt⟩  -- default value

  open TypeDecl

  /-
   - TODO: consider replacing the unwieldy `∀ s ∈ fields` maps in `pStruct` with
   - maps from `fin n` (which refer to the sorted fields). Use `fin.cons` and
   - `fin.tail` from `data.fin` in order to manipulate the maps like lists.
   -/
  inductive Val: TypeDecl → Type
   | pInt:  ℤ       → Val gInt
   | pStr:  string  → Val gStr
   | pErr:  string  → Val gErr
   | pBool: bool    → Val gBool
   | pPtr (t: TypeDecl)
          (address: option ℤ)
          : Val (gPtr t)
   | pArr (n: ℕ)
          (t: TypeDecl):
          (∀ s: fin n, Val (gPtr t)) → Val (gArr n t)
   | pStruct (name:     string)
              (fields:   finset string)
              (valtypes: ∀ s ∈ fields, TypeDecl)
              (vals:     ∀ s ∈ fields, Val (valtypes s H))
              : Val (gRef name)

  instance : ∀ t, decidable_eq (Val t) :=
    begin
    intros t a b, induction a generalizing b; cases b;
    try {{ apply decidable.is_false, rintro ⟨⟩}},
    {exact decidable_of_iff (a = b_1) (by simp) },
    {exact decidable_of_iff (a = b_1) (by simp) },
    {exact decidable_of_iff (a = b_1) (by simp) },
    {exact decidable_of_iff (a = b_1) (by simp) },
    {exact decidable_of_iff (a_address = b_address) (by simp) },
    {resetI,
       refine decidable_of_iff (∀ x , a_a x = b_a x) ( by {intros, split,
        {intros, simp [function.funext_iff], exact a},
        {intros, simp [function.funext_iff] at a, exact a x}})},
    {refine if h': a_fields = b_fields then _ else decidable.is_false
                                                   (by simp [h']),
     subst h', simp, resetI,

     refine if h'': a_valtypes = b_valtypes then _ else decidable.is_false
                                                          (by simp [h'']),
     subst h'', simp,
     refine decidable_of_iff (∀ x h, (a_vals x h = b_vals x h))
         (by {intros, split,
            {intros,  simp [function.funext_iff],exact a,},
            {intros, simp [function.funext_iff] at a, exact a x h} }),},

      end


  open Val

  def Val.bval: Val gBool → bool
   | (pBool x) := x
  def Val.ival: Val gInt → ℤ
   | (pInt x) := x
  def Val.sval: Val gStr → string
   | (pStr x) := x
  def Val.pval: Π {t}, Val (gPtr t) → option ℤ
   | _ (pPtr _ x) := x


  /-
   - Automatically coerce simple types
   -/
  instance bcoe: has_coe (Val gBool) bool := ⟨λ z, z.bval⟩
  instance bcoe': has_coe bool (Val gBool) := ⟨λ z, Val.pBool z⟩
  instance icoe: has_coe (Val gInt) ℤ := ⟨λ z, z.ival⟩
  instance icoe': has_coe ℤ (Val gInt) := ⟨λ z, Val.pInt z⟩
  instance scoe: has_coe (Val gStr) string := ⟨λ z, z.sval⟩
  instance scoe': has_coe string (Val gStr) := ⟨λ z, Val.pStr z⟩

  /-
   - Default inhabited value for Vals
   -/
  def inh: ∀ t, (Val t)
   | gInt        := pInt 0
   | gStr        := pStr ""
   | gErr        := pErr ""
   | gBool       := pBool ff
   | (gPtr x)    := pPtr x none
   | (gArr n t)  := pArr n t (λ _, pPtr t none)
   | (gRef name) := pStruct name ∅ (λ _ _, gInt) (λ _ _, pInt 0)

  instance: ∀ t, inhabited (Val t) := λ t, ⟨inh t⟩

  def Val.to_TypeDecl {t} (_: Val t): TypeDecl:= t

end language_types

section type_mapping

  open TypeDecl

  /-
   - Sometimes we don't know ahead of time if the type β that we're expecting
   - is actually equal to the type 'type_dict x' we are giving, so these as_type
   - functions handle this in a safe way.
   -/
  @[simp]
  def as_type  {dt: TypeDecl}
              (t: Val dt) (dt':TypeDecl): option (Val dt') :=
    if h: dt = dt' then some (by rw ← h; exact t) else none

  @[simp]
  def as_type_opt  {dt: TypeDecl}  (t: option (Val dt))
                  (dt':TypeDecl): option (Val dt') :=
      t >>= λ somet, @as_type dt somet dt'

  open Val

end type_mapping

section language_operators

  /-
   - Defining operators in Go
   -/
  @[derive decidable_eq]
  inductive Relop: Type | EQ | NEQ | LE

  @[derive decidable_eq]
  inductive Binop: Type | PLUS | MINUS | OR | AND

  @[derive decidable_eq]
  inductive Unop: Type | NOT | NEG

end language_operators

section gostructs
  open Val open TypeDecl

  /-
   - Cast a nat to an element of (fin n), fail if it's too large.
   -/
  def to_fin (n) (i:ℕ) : option (fin n) :=
    if h: i < n then some ⟨i,h⟩ else none

  /-
   - Helper for shrink
   -/
  def shrink' (f:finset string) (h1: f.nonempty) (ts : ∀ s ∈ f, TypeDecl):
        ∀ s ∈ (f.erase (f.min' h1)), TypeDecl := by {
          intros s h,
          rw finset.mem_erase at h,
          exact ts s h.2}

  /-
   - Some analogue to structural recursion for linear ordered finsets
   -/
  def shrink (f : finset string) (ts : ∀ s ∈ f, TypeDecl)
              (vals: ∀ s ∈ f, Val (ts s H))
              : (Σ (f': finset string) (ts': ∀ s ∈ f', TypeDecl),
                  ∀ s ∈ f', Val (ts' s H)) :=
    if h0: f = ∅ then ⟨f, ts, λ a b, inh (ts a b)⟩
    else
      have h1: f.nonempty := finset.nonempty_of_ne_empty h0,
      have h2: ∃ a, a ∈ f.min := finset.min_of_nonempty h1,
      have mxmem: f.min' h1 ∈ f := finset.min'_mem f h1,
      have mxtyp: TypeDecl := ts (f.min' h1) mxmem,

      have newvals: ∀ s ∈ (f.erase (f.min' h1)), Val ((shrink' f h1 ts) s H),
          by {intros s h',
          rw finset.mem_erase at h', dedup,
        exact vals s h'_1.2},
      ⟨f.erase (f.min' h1), shrink' f h1 ts, newvals⟩

  /-
   - Add a field, value pair to an existing Struct (helper for add_key)
   -/
    def add_key' (k: string) (t: TypeDecl) (val: Val t)
                (f: finset string) (ts: ∀ s ∈ f, TypeDecl)
                (v : ∀ s ∈ f, Val (ts s H))
                : Σ(fields: finset string) (typs:∀ s ∈ fields, TypeDecl ),
                  ∀ s ∈ fields, Val (typs s H) :=
      ⟨insert k f, λ s mem, if h: s = k then t else  begin
        apply ts s, -- changes goal to needing to prove s is in old fields
          rw finset.mem_insert at mem, -- mem of insert means s=k or s ∈ f
            simp only [h, false_or] at mem, -- rule out poss. of s=k with ¬h
            exact mem end
        , λ s mem,
      if h: s=k then by {subst h, simp, exact val} else  begin
        rw finset.mem_insert at mem, -- mem of insert means s=k or s ∈ f
        simp only [h, false_or] at mem, -- rule out poss. of s=k with ¬h
          have Q : (dite (s = k) (λ (h : s = k), t) (λ (h : ¬s = k), ts s mem)
                    = ts s _), by { simp [h]},
        rw Q, exact v s mem
       end⟩

  def add_key: Π (s) (t), Val t → string
              → Val (gRef s)  → Val (gRef s)
      | s t pt key (pStruct _ f' ts' vs') :=
    match add_key' key t pt f' ts' vs' with
      | ⟨f, ts, vs⟩ := (pStruct _ f ts vs)
     end

  /-
   - Convenience constructor for GoStruct
   - An arbitrary value can be used for the image of a map with an empty domain
   -/
  def list_to_struct: Π(s) , list (string × (Σ t, Val t))
                          →  Val (gRef s)
   | s  []        := inh (gRef s)
   | n ((k,⟨t,v⟩)::tl) := add_key n t v k (list_to_struct n tl)


  @[simp]
  def Val.get: Π{s}, Val (gRef s) → string → option (Σ t, Val t)
    | _ (pStruct _ f _ v) key := if h: key ∈ f then some (⟨_, v _ h⟩) else none

  @[simp]
  def Val.name {s} (_: Val (gRef s)): string := s

  @[simp]
  def Val.len : ∀ {s}, Val (gRef s) → ℕ
   | _ (pStruct _ f _ _) := f.card

  def Val.fieldlist: Π{s}, Val (gRef s) → list string
   | _ (pStruct _ f _ _) := @finset.sort string (λ s1 s2, s1 <= s2) _ _ _ _ f

  /-
   - Update a field with a value (error if key doesn't exist or different type)
   -/
  def Val.update: Π {s: string} (α: TypeDecl),
                        Val (gRef s) → string → Val α → option (Val (gRef s))
   | s α (pStruct _ fs ts vs) f v :=
      if h: f ∈ fs then
        if (vs f h).to_TypeDecl = α then
          some $ add_key s _ v f (pStruct _ fs ts vs)
        else none
      else none

end gostructs

section to_strings

  open TypeDecl open Val open nat

  def str_gottypeddecl: TypeDecl → string
    | gInt := "Int"
    | gStr := "Str"
    | gErr := "Error"
    | gBool := "Bool"
    | (gPtr t) := "*" ++ str_gottypeddecl t
    | (gArr n t) := "["++to_string n ++"]" ++ str_gottypeddecl t
    | (gRef s) := s
  instance: has_to_string TypeDecl := ⟨str_gottypeddecl⟩
  instance: has_repr      TypeDecl := ⟨str_gottypeddecl⟩

  /-
  - Rendering Vals works but relies on sorry in two places to show that
  - it terminates. The struct's fields are printed in alphabetical order.
  -/
  meta mutual def str_ptype, str_arr, str_fields
  with str_ptype: ∀ t, Val t → string
   | _ (pInt p)            := to_string p
   | _ (pStr p)            := to_string p
   | _ (pErr p)            := to_string p
   | _ (pBool p)           := to_string p
   | _ (pPtr _ v)            :=  v.elim "?" to_string
   | (gArr n t) (pArr _ _ v) := "[" ++ str_arr n v ++ "]"
   | _ (@pStruct name f t v) := name ++"{"++ str_fields f t v ++"}"

  with str_arr: Π{n} {t}, ℕ → (fin n → Val t) → string
   | _ _ 0 _ := ""
   | n t (succ i) a := (to_fin n i).elim "" (λ x, str_ptype t $ a x)
                        ++ str_arr i a
 with str_fields: Π(f:finset string) (ts: (∀ s ∈ f, TypeDecl)),
               (∀ s ∈ f, Val (ts s H))  → string
  | f ts v :=
      begin
      have e: decidable (f = ∅) := finset.has_decidable_eq f ∅,
      cases e with hf ht,
          {have h1: f.nonempty := finset.nonempty_of_ne_empty hf,
           have head: string := f.min' h1 ++ ": " ++ (
                    str_ptype (ts (f.min' h1) (finset.min'_mem f h1))
                              (v (f.min' h1) (finset.min'_mem f h1)))
                  ++ if f.card > 1 then ", " else "",
            exact head ++ (
                match shrink f ts v with
                 | ⟨a,b,c⟩ := str_fields a b c
                end )},
          {exact ""}
        end

  meta instance: ∀ t, has_to_string (Val t) := λ t, ⟨str_ptype t⟩
  meta instance: ∀ t, has_repr (Val t) := λ t, ⟨str_ptype t⟩


end to_strings

section other_instances

  open TypeDecl open Val

  instance int_le: has_le (Val gInt) := ⟨λ a b, a.ival <= b.ival⟩

  instance int_add:    has_add    (Val gInt) := ⟨λ a b, pInt $ a.ival + b.ival⟩
  instance int_lt:     has_lt     (Val gInt) := ⟨λ a b, a.ival < b.ival⟩
  instance int_zero:   has_zero   (Val gInt) := ⟨pInt 0⟩
  instance int_one:    has_one    (Val gInt) := ⟨pInt 1⟩
  instance int_neg:    has_neg    (Val gInt) := ⟨λ a, pInt $ -a.ival⟩
  instance int_sub:    has_sub    (Val gInt) := ⟨λ a b, pInt $ a.ival - b.ival⟩
  instance str_le:     has_le     (Val gStr) := ⟨λ a b, a.sval <= b.sval⟩
  instance str_append: has_append (Val gStr) := ⟨λ a b, pStr $ a.sval ++ b.sval⟩

  instance ptr_zero: Π s, has_zero (Val (gPtr s)) := λ _, ⟨pPtr _ (some 0)⟩
  instance ptr_one:  Π s, has_one  (Val (gPtr s)) := λ _, ⟨pPtr _ (some 1)⟩
  instance ptr_neg:  Π s, has_neg  (Val (gPtr s)) := λ _, ⟨
      λ p, match p with
       | (pPtr _ val) := pPtr _ $ val >>= some ∘ int.neg -- negate if not none
      end⟩
  instance ptr_sub:  Π s, has_sub  (Val (gPtr s)) := λ _, ⟨
      λ p1 p2, match p1,p2 with
       | (pPtr _ val1), (pPtr _ val2) := pPtr _ (do v1 ← val1, v2 ← val2,
                                                    some (v1 - v2))
      end⟩
  instance ptr_add:  Π s, has_add  (Val (gPtr s)) := λ _, ⟨
      λ p1 p2, match p1,p2 with
       | (pPtr _ val1), (pPtr _ val2) := pPtr _ (do v1 ← val1, v2 ← val2,
                                                    some (v1 + v2))
      end⟩
end other_instances