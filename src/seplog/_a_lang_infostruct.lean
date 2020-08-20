import data.finset.basic
import data.finset.sort
import data.finset.fold
import data.finmap
import data.fintype.basic
import tactic.linarith

/-
 - Model of Golang.
 - This version explores a strategy for putting the full field information
 - of a struct within its own type declaration. This would allow one to ensure
 - the struct is correct (and initiate instances of it) without refering to a
 - global context.
 - The downside to this approach is that you cannot have self-referential
 - structs, e.g. Linked List.
 -/

  inductive TypeDecl: Type
   | gInt:  TypeDecl
   | gStr:  TypeDecl
   | gErr:  TypeDecl
   | gBool: TypeDecl
   | gPtr:  TypeDecl → TypeDecl
   | gArr: ℕ → TypeDecl → TypeDecl
   | gStruct  (name: string) (fields: finset string)
              (vals: ∀ s ∈ fields, TypeDecl) : TypeDecl

  instance : decidable_eq TypeDecl :=
    begin
    intros a b, induction a generalizing b; cases b;
    try {{ apply decidable.is_false, rintro ⟨⟩ }},
    { simp [], exact decidable.true  },
    { simp [], exact decidable.true },
    { simp [], exact decidable.true },
    { simp [], exact decidable.true },
    {simp, exact (a_ih b), },
    { simp, apply @and.decidable (a_a=b_a) (a_a_1= b_a_1)
          (nat.decidable_eq a_a b_a) (a_ih b_a_1)},
    {refine if h: a_name = b_name then _ else decidable.is_false (by simp [h]),
     refine if h': a_fields = b_fields then _ else decidable.is_false (by simp [h']),
     subst h, subst h', simp, resetI,
     refine decidable_of_iff (∀ x h, (a_vals x h = b_vals x h))
         (by {intros, split,
            {intros,  simp [function.funext_iff],exact a,},
            {intros, simp [function.funext_iff] at a, exact a x h} }),},
    end

  open TypeDecl
  instance: inhabited TypeDecl := ⟨gInt⟩

  inductive PrimType: TypeDecl → Type
   | pInt:  ℤ → PrimType gInt
   | pStr:  string → PrimType gStr
   | pErr:  string → PrimType gErr
   | pBool: bool → PrimType gBool
   | pPtr (t: TypeDecl): ℤ → PrimType (gPtr t)
   | pArr (t: TypeDecl) (n:ℕ): (∀ s: fin n, PrimType t)
                               → PrimType (gArr n t)
   | pStruct  (name: string) (fields: finset string)
              (valtypes: ∀ s ∈ fields, TypeDecl)
              (vals: ∀ s ∈ fields, PrimType (valtypes s H))
              : PrimType (@gStruct name fields valtypes)
  open PrimType
  instance : ∀ t, decidable_eq (PrimType t) :=
    begin
    intros t a b, induction a generalizing b; cases b;
    try {{ apply decidable.is_false, rintro ⟨⟩ }},
    { exact decidable_of_iff (a = b_1) (by simp) },
    { exact decidable_of_iff (a = b_1) (by simp) },
    { exact decidable_of_iff (a = b_1) (by simp) },
    { exact decidable_of_iff (a = b_1) (by simp) },
    { exact decidable_of_iff (a_a = b_a) (by simp) },
    {resetI,
       refine decidable_of_iff (∀ x , a_a x = b_a x) ( by {intros, split,
        {intros, simp [function.funext_iff], exact a},
        {intros, simp [function.funext_iff] at a, exact a x}})},
    { resetI, refine decidable_of_iff (∀ x h, a_vals x h = b_vals x h)
        (by {intros, split,
        {intros, simp [function.funext_iff], exact a},
        {intros, simp [function.funext_iff] at a, exact a x h}}),},
    end

  def inh: ∀ t, (PrimType t)
   | gInt := pInt 0
   | gStr := pStr ""
   | gErr := pErr ""
   | gBool := pBool ff
   | (gPtr x) := @pPtr x 0
   | (gArr n t) := @pArr t n (λ _, inh t)
   | (@gStruct  name fs vs) := @pStruct _ _ _
      (λ x h, (have H: (vs x h).sizeof <
                        1 + name.length + finset.sizeof string fs := sorry,
      inh (vs x h)))

  instance: ∀ t, inhabited (PrimType t):= λ t, ⟨inh t⟩

  @[derive decidable_eq]
  structure Ptr (t: TypeDecl) := (val: ℤ)
  @[derive decidable_eq]
  structure Arr (n: ℕ) (t: TypeDecl) := (vals: (∀ s: fin n, PrimType t))

  structure Struct (name: string) (fields: finset string)
                         (valtypes: ∀ s ∈ fields, TypeDecl)
                          :=
    (vals: ∀ s ∈ fields, PrimType (valtypes s H))

lemma strext {name} {fields} {valtypes} (a b: Struct  name fields valtypes)
                (h : a.vals=b.vals) : a = b := begin
                  cases a, cases b, simp at h, simp, exact h
        end

  def type_dict: TypeDecl → Type
      | gStr    := string
      | gErr    := string
      | gInt    := ℤ
      | gBool   := bool
      | (gPtr t):= Ptr t
      | (gArr n t):= Arr n t
      | (gStruct name fs vs):= Struct name fs vs

  @[simp]
  def to_td: ∀ t, (PrimType t) → (type_dict t)
   | gInt            (pInt x)           := x
   | gStr            (pStr x)           := x
   | gErr            (pErr x)           := x
   | gBool           (pBool x)          := x
   | (gPtr _)        (pPtr _ x)         := Ptr.mk x
   | (gArr _ t)      (pArr _ _ xs)      := Arr.mk xs
   | (gStruct _ _ _) (pStruct _ _ _ xs) :=  ⟨xs⟩

  @[simp]
  def from_td: ∀ t, (type_dict t) → (PrimType t)
   | gInt x := pInt x
   | gStr x := pStr x
   | gErr x := pErr x
   | gBool x := pBool x
   | (gPtr t) x := pPtr t x.val
   | (gArr n t) x := pArr t n x.vals
   | (gStruct n fs vs) x := pStruct n fs vs x.vals

  /-
   - Bijection between the PrimType representation and Lean types
   -/
  def td_bij: ∀ t:TypeDecl, equiv (PrimType t) (type_dict t) := λ t,
  { to_fun    := to_td t,
    inv_fun   := from_td t,
    left_inv  := by {rintro ⟨n⟩; refl},
    right_inv := by {induction t;
      {unfold function.right_inverse,unfold function.left_inverse, intros x,
       cases x; simp  },
    }}



  def PrimType.to_typedecl  {t} (x: PrimType t): TypeDecl := t

  /-
   - Sometimes we don't know ahead of time if the type β that we're expecting
   - is actually equal to the type 'type_dict x' we are giving, so these as_type
   - functions handle this in a safe way.
   -/
  @[simp]
  def as_type  {dt: TypeDecl}
              (t: type_dict dt) (dt':TypeDecl): option (type_dict dt') :=
    if h: dt = dt' then some (by rw ← h; exact t) else none

  @[simp]
  def as_type_opt  {dt: TypeDecl}  (t: option (type_dict dt))
                  (dt': TypeDecl): option (type_dict dt') :=
      t >>= λ somet, @as_type dt somet dt'

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
  open PrimType open nat


  lemma ltsucc : ∀ n, n < n+1 :=
    by simp only [nat.succ_pos', forall_const, lt_add_iff_pos_right]

  def to_fin (n) (i:ℕ) : option (fin n) :=
    if h: i < n then some ⟨i,h⟩ else none

  def shrink' (f:finset string) (h1: f.nonempty) (ts : ∀ s ∈ f, TypeDecl):
        ∀ s ∈ (f.erase (f.min' h1)), TypeDecl := by {
          intros s h,
          rw finset.mem_erase at h,
          exact ts s h.2}

  /-
   - Some analogue to structural recursion for linear ordered finsets
   -/
  def shrink (f : finset string) (ts : ∀ s ∈ f, TypeDecl)
              (vals: ∀ s ∈ f, PrimType (ts s H))
              : (Σ (f': finset string) (ts': ∀ s ∈ f', TypeDecl),
                  ∀ s ∈ f', PrimType (ts' s H)) :=
    if h0: f = ∅ then ⟨f, ts, λ a b, inh (ts a b)⟩
    else
      have h1: f.nonempty := finset.nonempty_of_ne_empty h0,
      have h2: ∃ a, a ∈ f.min := finset.min_of_nonempty h1,
      have mxmem: f.min' h1 ∈ f := finset.min'_mem f h1,
      have mxtyp: TypeDecl := ts (f.min' h1) mxmem,

      have newvals: ∀ s ∈ (f.erase (f.min' h1)), PrimType ((shrink' f h1 ts) s H), by {
          intros s h',
          rw finset.mem_erase at h', dedup,
        exact vals s h'_1.2},

      ⟨f.erase (f.min' h1), shrink' f h1 ts, newvals⟩
  /-
   - Add a field, value pair to an existing Struct (helper for add_key)
   -/
    def add_key' (k: string) (t: TypeDecl) (val: PrimType t)
                (f: finset string) (ts: ∀ s ∈ f, TypeDecl)
                (v : ∀ s ∈ f, PrimType (ts s H))
                : Σ(fields: finset string) (typs:∀ s ∈ fields, TypeDecl ),
                  ∀ s ∈ fields, PrimType (typs s H) :=
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

  def add_key: Π (s) (t), PrimType t → string
              → (Σ f v, Struct s f v) → (Σ f v, Struct s f v)
      | s t pt key ⟨f', ts', ⟨vs'⟩⟩  :=
    match add_key' key t pt f' ts' vs' with
      | ⟨f, ts, vs⟩ := ⟨f, ts, ⟨vs⟩⟩
     end

  /-
   - Convenience constructor for GoStruct
   - An arbitrary value can be used for the image of a map with an empty domain
   -/
  def GoStruct.from_list: Π(s) , list (string × (Σ t, PrimType t))
                          → Σ (f) (v), Struct s f v
   | s  []        := ⟨∅, (λ _ _, gBool), ⟨λ _ _, pBool ff⟩⟩ -- impossible
   | n ((k,⟨t,v⟩)::tl) := add_key n t v k (GoStruct.from_list n tl)


end gostructs

section to_strings

open nat
  def str_typeddecl: TypeDecl → string
    | gInt := "Int"
    | gStr := "Str"
    | gErr := "Error"
    | gBool := "Bool"
    | (gPtr t) := "*" ++ str_typeddecl t
    | (gArr n t) := "["++to_string n ++"]" ++ str_typeddecl t
    | (gStruct s _ _) := s
  instance: has_to_string TypeDecl := ⟨str_typeddecl⟩
  instance: has_repr      TypeDecl := ⟨str_typeddecl⟩

  /-
  - Rendering GoPrimTypes works but relies on sorry in two places to show that
  - it terminates. The struct's fields are printed in alphabetical order.
  -/
  meta mutual def str_ptype, str_arr, str_fields
  with str_ptype: ∀ t, PrimType t → string
   | _ (pInt p)            := to_string p
   | _ (pStr p)            := to_string p
   | _ (pErr p)            := to_string p
   | _ (pBool p)           := to_string p
   | _ (pPtr t v)            := "*" ++ to_string t ++ "@" ++ to_string v
   | (gArr n t) (pArr _ _ v) := "[" ++ str_arr n v ++ "]"
   | _ (@pStruct name f t v) := name ++"{"++ str_fields f t v ++"}"

  with str_arr: Π{n} {t}, ℕ → (fin n → PrimType t) → string
   | _ _ 0 _ := ""
   | n t (succ i) a := (to_fin n i).elim "" (λ x, str_ptype t $ a x)
                        ++ str_arr i a
 with str_fields: Π(f:finset string) (ts: (∀ s ∈ f, TypeDecl)),
               (∀ s ∈ f, PrimType (ts s H))  → string
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

  meta def str_gstruct (s) (f) (v) (x: Struct s f v): string :=
    str_ptype _ (pStruct s f v x.vals)

  meta instance :∀ t,  has_to_string (PrimType t):= λ t, ⟨str_ptype t⟩
  meta instance :∀ t,  has_to_string (Ptr t):=
    λ t, ⟨λ ⟨z⟩, str_ptype (gPtr t) (pPtr t z)⟩
  meta instance :∀ n t,  has_to_string (Arr n t):=
    λ n t, ⟨λ ⟨z⟩, str_ptype (gArr n t) (pArr t n z)⟩

  meta instance: Π(s) (f) (v), has_repr (Struct s f v)
    | s f v := ⟨str_gstruct s f v⟩.
  meta instance: Π(s) (f) (v), has_to_string (Struct s f v)
    | s f v := ⟨str_gstruct s f v⟩

 meta instance type_dict_to_string: Π(x:TypeDecl), has_to_string (type_dict x)
    | gStr     := string.has_to_string
    | gErr     := string.has_to_string
    | gInt     := int.has_to_string
    | gBool    := bool.has_to_string
    | (gPtr t) := (Ptr.has_to_string t)
    | (gArr n t) := (Arr.has_to_string n t)
    | (gStruct n f v) := (Struct.has_to_string n f v)

end to_strings

section other_instances

  open TypeDecl

  instance int_le:     has_le     (type_dict gInt) := int.has_le
  instance int_add:    has_add    (type_dict gInt) := int.has_add
  instance int_lt:     has_lt     (type_dict gInt) := int.has_lt
  instance int_zero:   has_zero   (type_dict gInt) := int.has_zero
  instance int_one:    has_one    (type_dict gInt) := int.has_one
  instance int_neg:    has_neg    (type_dict gInt) := int.has_neg
  instance int_sub:    has_sub    (type_dict gInt) := int.has_sub
  instance str_le:     has_le     (type_dict gStr) := string.has_le
  instance str_append: has_append (type_dict gStr) := string.has_append

end other_instances


/-

--   /-
--    - Two lemmas about fieldlist which help prove define GoStruct.index
--    -/
--   lemma fl_len_eq {s} (x: GoStruct s): x.fieldlist.length = x.len := begin
--     induction x,
--     simp, unfold GoStruct.fieldlist, simp,
--   end

--   lemma fl_mem {s} {x: GoStruct s} {key: string}:
--                key ∈ x.fieldlist → key ∈ x.fields  := begin
--     intros H, induction x,
--     unfold GoStruct.fieldlist at H, simp at H, simp, exact H
--   end

--   /-
--    - Alternative of nth_le that also returns a proof that the return element is a
--    - member of the original list being indexed.
--    -/
--   @[simp]
--   def nth_le_mem : Π {α: Type} (l : list α) (n),
--                       n < l.length → psigma (λ a:α, a ∈ l)
--    | _ []       n     h := absurd h (nat.not_lt_zero n)
--    | _ (a :: l) 0     h := ⟨a, by {simp}⟩
--    | _ (a :: l) (n+1) h :=
--       match (nth_le_mem l n (nat.le_of_succ_le_succ h)) with
--             | ⟨q, r⟩ := ⟨q, list.mem_cons_of_mem a r⟩
--       end

--   lemma ltsucc : ∀ n, n < n+1 :=
--     by simp only [nat.succ_pos', forall_const, lt_add_iff_pos_right]

--   /-
--    - Given an index into the (sorted) fields, return a string and a proof that it
--    - is a member of the finset.
--    -/
--   def GoStruct.index {name} {n:ℕ} (x: GoStruct name)
--                      (H: n < x.len) : psigma (λ f, f ∈ x.fields) := begin
--     have z := nth_le_mem x.fieldlist n
--                                     (by {rw fl_len_eq x, exact H}),
--     exact ⟨z.1, fl_mem z.2⟩
--   end

--   /-
--    - Helper function from GoStruct.structvals
--    -/
--   def structvals': Π {n:ℕ} {s: string} {x:GoStruct s},
--                     n < x.len → list (string × GoPrimType)
--     |  0 _  _ _  := []
--     |  (n+1) _ x h := match x.index h with
--                           | ⟨u,v ⟩ :=  (u, x.vals u v) ::
--                                       structvals' (lt.trans (ltsucc n) h)
--                       end

--   /-
--    - key sorted list of values
--    -/
--   def GoStruct.pairs {s} (x: GoStruct s) : list (string × GoPrimType) :=
--     begin
--       cases h : x.len with n,
--         {exact []},
--       {have H: x.len -1 < x.len, by {rw h, simp, exact ltsucc n},
--         exact structvals' H}
--   end

--   /-
--    - Access a field of a struct instance with an expected type
--    -/
--   def check_member_fields : Π(α: GoTypeDecl) {s: string},
--       option (GoStruct s) → string → option (type_dict α)
--     | _ _ none                          _     := none
--     | α _ (some s) field := GoStruct.get s field >>=
--                               λx, as_type (x.to_gotype.2) α


-/