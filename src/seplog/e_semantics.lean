import seplog.d_context
import seplog.b_memory

section evaluation
  open Relop open Binop open Val open TypeDecl open Ctx open Val
  open Store
  /-
   - Lemmas needed to fold && over a finset of bools (in struct_eq)
   -/
  section boolean_and

    theorem band_comm: ∀ (a b: bool), a && b  = b && a := begin
      intros, induction a ; induction b; tauto,
    end

    instance: is_commutative bool band := ⟨band_comm⟩

    theorem band_assoc: ∀ (a b c: bool), (a && b) && c  = a && (b && c)
      := begin
      intros, cases a; cases b; cases c; tauto,
    end

    instance: is_associative bool band := ⟨band_assoc⟩

  end boolean_and

  /-
   - Define the behavior of relational operators (none means failure)
   - We are not modeling memory management explicitly, so we throw a
   - failure if comparing non-nil pointers for equality or LEQ, even
   - if these are well-defined in Go.
   -/
  def relop_eval: Π{α: TypeDecl},
      Relop → option (Val α) → option (Val α) → option bool
   | _        _   none      _       := none
   | _        _   _        none     := none
   | gBool    EQ  (some x) (some y) := some $ x = y
   | gBool    NEQ (some x) (some y) := some $ ¬ x = y
   | gBool    LEQ (some x) (some y) := some $ (bnot x.bval) || y.bval
   | gInt     EQ  (some x) (some y) := some $ x = y
   | gInt     NEQ (some x) (some y) := some $ ¬ (x = y)
   | gInt     LEQ (some x) (some y) := some $ x.ival <= y.ival
   | gStr     EQ  (some x) (some y) := some $ x = y
   | gStr     NEQ (some x) (some y) := some $ ¬(eq x y)
   | gStr     LEQ (some x) (some y) := some $ x <= y
   | gErr     EQ  (some x) (some y) := some $ x = y
   | gErr     NEQ (some x) (some y) := some $ ¬(eq x y)
   | gErr     LEQ _          _      := none
   | (gRef s) EQ  (some x) (some y) := some $  x = y
   | (gRef s) NEQ (some x) (some y) := some ¬(x = y)
   | (gRef s) LEQ _          _      := none
   | (gPtr s) EQ  (some x) (some y) := some $ x = y
   | (gPtr s) NEQ (some x) (some y) := some $ ¬ x = y
   | (gPtr s) _   _        _        := none
   | (gArr n t) _ _          _      := none

  /-
   - Define thse behavior of binary operators
   -/
  def binop_eval: Π{α: TypeDecl},
    Binop → option (Val α) → option (Val α) → option (Val α)
   | _        _     none       _          := none
   | _        _     _          none       := none
   | (gRef _) _     _          _          := none
   | gErr     _     _          _          := none
   | gBool    OR    (some x) (some y) := some $ pBool $ x.bval || y.bval
   | gBool    AND   (some x) (some y) := some $ pBool $ x.bval && y.bval
   | gBool    _     _          _          := none
   | gInt     PLUS  (some x) (some y) := if  (x+y >  2147483647)
                                              || (x+y < -2147483648)
                                            then none  -- overflow
                                            else some $ x + y
   | gInt     MINUS (some x) (some y) := if  (x-y >  2147483647)
                                              || (x-y < -2147483648)
                                            then none  -- overflow
                                            else some $ x - y
   | gInt     _     _          _          := none
   | gStr     PLUS  (some x) (some y) := some $ x ++ y
   | gStr     _     _          _          := none
   | (gPtr _) _     _          _          := none
   | (gArr _ _) _     _          _          := none

   def unop_eval: Π{α: TypeDecl}, Unop → option (Val α) → option (Val α)
    | gInt   NEG  (some x) := some $ -x
    | gBool  NOT  (some x) := some $ pBool $ bnot x.bval
    | _      _    _        := none

  open Expr
  @[simp]
  def eval: Π{α: TypeDecl}, Expr α → Store → option (Val α)
   | _ (@const _ x)     _     := some x       -- constant
   | _ (getvar v)       e     := get_var v e  -- look to env
   | _ (@relop α o x y) e     := relop_eval o (@eval α x e) (@eval α y e)
                                  >>= some ∘ pBool
   | _ (@binop α o x y) e     := binop_eval o (@eval α x e) (@eval α y e)
   | _ (@unop α o x)    e     := unop_eval o (@eval α x e)
   | _ (@get_field s α x f) e := do t      ← eval x e,
                                    ⟨_, v⟩ ← t.get f,
                                    as_type v α
   | _ (@update_field s α xstr field val) e := do
      structval ← eval xstr e,
      fieldval  ← eval val e,
      structval.update α field fieldval

def eval_generic {α: TypeDecl} (s: Store) (x: Expr α)
                : option (Σ β, Val β) :=
  eval x s >>= λ res, some ⟨_, res⟩

end evaluation


section semantics
  open cmd open TypeDecl open Expr

  /-
   - Typecheck the called arguments against a signature and make a list
   - that can be used by Store.updates
   -/
  def input_updates: Store → list (Σ α, Expr α) → list (string × TypeDecl)
                    → option (list (string × (Σ α, Val α)))
    | _ []                    []              := some []
    | _ []                    _               := none
    | _ _                     []              := none
    | s (⟨vtype, x⟩::vs) ((sname, stype)::ss) := do
      rest <- input_updates s vs ss,
      val ← eval x s,
      if vtype = stype then some $ ((sname, ⟨_, val⟩))::rest  else none

  /-
   - Construct inner context for a method call
   -/
  def method_input_ctx: Ctx → Sig → list (Σ α, Expr α) → Π{struct},
                        Expr (gPtr (gRef struct)) ⊕ Expr (gRef struct)
                        → option Ctx
    | ⟨s,h,d⟩ ⟨sargs, _, rec, ptr⟩ args str callee := do
        updates ← input_updates s args (from_pairmap sargs),
        callee' ← callee.elim (eval_generic s) (eval_generic s),
        let call_type := (if ptr then gPtr (gRef str) else gRef str),
        callee'' ← as_type callee'.2 call_type,
        let s' := Store.from_list ((rec, ⟨_, callee''⟩)::updates),
        some ⟨s', h, d⟩

  /-
   - Given an outer context and a result context from a method call, use the
   - of the method to appropriately update the outer context.
   -/
  def method_update_ctx: Ctx → Ctx → Sig → list (Σ α, Var α) → option Ctx
    | ⟨s, h, d⟩ ⟨s', h', _⟩ ⟨_,ret,_,_⟩ retv := do
      let retlist := from_pairmap ret,
      updates ← input_updates s'
        (retlist.map (λ name_typ,  ⟨_, @getvar name_typ.2 ⟨name_typ.1⟩⟩))
        (retv.map (λ v, (v.2.name,v.1))),
      some ⟨s.updates updates, h', d⟩

  inductive exec: option Ctx → cmd → option Ctx → Prop
    | exec_none: ∀ c, exec none c none

    | exec_skip: ∀ s, exec (some s) skip (some s)
    /-
     - Assign
     -/
      | exec_assign: ∀ {α:TypeDecl} (s:Store) (h:Heap) (d: Decls) (x: Var α)
                          (e: Expr α) (v: Val α),
        (eval e s) = some v
              → exec (some (s, h, d)) (x ⇐ e) (some (s.update v x.name, h, d))

      | exec_assign_fail: ∀ {α:TypeDecl} (s:Store) (h:Heap) (d: Decls)
                            (x: Var α) (e: Expr α),
        (eval e s) = none
              → exec (some (s, h, d)) (x ⇐ e) none
    /-
     - Lookup
     -/
      | exec_lookup: ∀ {α: TypeDecl} (s: Store) (h: Heap) (x: Var α) (d: Decls)
                          (e: Expr (gPtr α)) (p: Address) (v: Val α),
        val2loc (eval e s) = some p → -- the relative int is cast to a location
        h.lookup p = some v →         -- extract the corresponding cell contents
        exec (some (s, h, d)) (x ↩ e) (some (s.update v x.name, h, d))

      | exec_lookup_err: ∀ {α: TypeDecl} (s: Store) (h: Heap) (x: Var α)
                              (e: Expr (gPtr α)) (p: Address) (d: Decls),
        val2loc (eval e s) = some p →
        h.lookup p = @none (Val α) → -- mem location not allocated
        exec (some (s, h, d)) (x ↩ e) none

      -- Lookup fails due to pointer expression failing
      | exec_lookup_err_px: ∀ {α: TypeDecl} (s: Store) (h: Heap) (x: Var α)
                              (e: Expr (gPtr α)) (d: Decls),
        val2loc (eval e s) = none → exec (some (s, h, d)) (x ↩ e) none
    /-
     - Mutation
     -/
      -- Successful mutation defined by heap.update
      | exec_mutation: ∀ {α: TypeDecl} (s: Store) (h: Heap)
                            (e: Expr (gPtr α)) (e': Expr α)
                            (p: Address) (v v2: Val α) (d: Decls),
        val2loc (eval e s) = some p → -- compute the address
        h.lookup p = some v2 → -- Check the address is assigned (ignore val)
        (eval e' s) = some v → -- compute the new value to point to\

        exec (some (s, h, d)) (e ≪ e') (some (s, h.update v p, d))

        -- Mutation fails because of looking at null pointer
      | exec_mutation_err: ∀ {α: TypeDecl} (s: Store) (h: Heap) (d: Decls)
                            (e: Expr (gPtr α)) (e': Expr α) (p: Address),
        val2loc (eval e s) = some p →
        h.lookup p = @none (Val α) →
        exec (some (s, h, d)) (e ≪ e') none

        -- Mutation fails due to pointer expression failing
      | exec_mutation_err_px: ∀ {α: TypeDecl} (s: Store) (h: Heap) (d: Decls)
                            (e: Expr (gPtr α)) (e': Expr α),
        val2loc (eval e s) = none → exec (some (s, h, d)) (e ≪ e') none

      | exec_seq: ∀ s s' s'' c d,
        exec s c s' → exec s' d s'' → exec s (c ∣ d) s''

    /-
     - While
     -/
      | exec_while_true: ∀ (s: Store) (h: Heap) (d: Decls) (s' s'': Ctx)
                            (b: Expr gBool) (c: cmd) ,
        eval b s = some tt →
        exec (some (s, h, d)) c s' →
        exec s' (while b c) s'' →
        exec (some (s, h, d)) (while b c) s''

      | exec_while_false: ∀ (s: Store) (h: Heap) (d: Decls) (b: Expr gBool)
                            (c: cmd),
        eval b s = some ff →
        exec (some (s, h, d)) (while b c) (some (s, h, d))

      | exec_while_err: ∀ (s: Store) (h: Heap) (d: Decls) (b: Expr gBool)
                          (c: cmd),
        eval b s = none → exec (some (s, h, d)) (while b c) none
    /-
     - If then else
     -/
      | exec_ifte_true: ∀ (b: Expr gBool) (x y: cmd) (s: Store) (h: Heap)
                          (d: Decls) s',
        eval b s = some tt →
        exec (some (s, h, d)) x s' →
        exec (some (s, h, d)) (ifte b x y) s'

      | exec_ifte_false: ∀ (b: Expr gBool) (c d: cmd) (s: Store) (h: Heap)
                          (d': Decls) s',
        eval b s = some ff →
        exec (some (s, h, d')) d s' →
        exec (some (s, h, d')) (ifte b  c  d) s'

      | exec_ifte_err: ∀ (b: Expr gBool) (c d: cmd) (s: Store) (h: Heap)
                        (d': Decls),
        eval b s = none →
        exec (some (s, h, d')) (ifte b  c  d) none

  /- Needed if malloc and free are included

    | exec_malloc: ∀ {α: TypeDecl} (s :Store) (h: Heap ) (x: Var (gPtr α))
                      (e: Expr α) (n: Address) (v: Val α),
      eval e s = some v →
      (h # Heap.singleton n v) →
      exec (some (s, h)) (malloc x e)
          (some (@Store.update s (gPtr α) n.val x.name,
                h ++ Heap.singleton n v))

    | exec_malloc_err: ∀ {α: TypeDecl} (s :Store) (h: Heap ) (x: Var (gPtr α))
                        (e: Expr α) (n: Address) (v: Val α),
      eval e s = none →  exec (some (s, h)) (malloc x e) none

    | exec_free: ∀ {α: TypeDecl} (s :Store) (h: Heap ) (e: Expr (gPtr α))
                  (val: Val α) (ptr: Address),
      val2loc (eval e s) = some ptr  → h.lookup ptr = some val →
        exec (some (s, h))  (free e) (some (s, h.erase ptr))

    -- Free fails because there is nothing in the heap at the pointer
    | exec_free_err: ∀ {α: TypeDecl} (s :Store) (h: Heap ) (e: Expr (gPtr α))
                      (val: Val α) (ptr: Address),
      val2loc (eval e s) = some ptr  → h.lookup ptr = some val →
        exec (some (s, h))  (free e) (some (s, h.erase ptr))

    -- Free fails because the pointer expression is erroneous
    | exec_free_err_px: ∀ {α: TypeDecl} (s: Store) (h: Heap)
                          (e: Expr (gPtr α)),
      val2loc (eval e s) = none →
        exec (some (s, h))  (free e) none
  -/


  /-
   - Alternative to "exec" which actually runs a program. Because this may not
   - terminate, it is tagged as "meta".
   -/
  meta def compute: Ctx → cmd → option Ctx
    | s skip := some s

    | s (v ⇐ x) := eval x s.1 >>= λ xv, s.update_store
                                         (s.1.update xv v.name)

    | s (v ↩ x) := do  p ← val2loc (eval x s.1),
                       z ← @Heap.lookup v.gotype s.2.1 p,
                       s.update_store (s.1.update z v.name)

    | s (v ≪ x) := do p ← val2loc (eval v s.1),
                       _ ← @Heap.lookup x.gotype s.2.1 p,
                       v ← @eval x.gotype x s.1,
                       s.update_heap (s.2.1.update v p)

    | s (c ∣ d) := compute s c >>= λ s', compute s' d

    | s (while b c) := eval b s.1 >>= λ bv, if bv = tt
          then (compute s c) >>= λ c', compute c' (while b c)
          else s

    | s (ifte b c d) := eval b s.1 >>= λ bv, compute s (if bv = tt
                                                        then c else d)

    | s (@declare (α) x) := do dval ← default α s.2.2,
                               s.update_store (s.1.update dval x.name)

    | s (@new (α) x) := do
      pval ← default α s.2.2,            -- create a value to initialize with
      val  ← as_type pval α,             -- enforce correct type
      let (h,p) := s.2.1.insert α val,   -- insert into heap + get ptr value
      compute (s.update_heap h)          -- store the value to the ptr
              (x ⇐ (@Expr.const (gPtr α) p.val))

     | s (@call str callee meth args ret) := do
        (sig, prog) ← s.method str meth,
        input_ctx   ← method_input_ctx s sig args callee,
        new_ctx     ← compute input_ctx prog ,
        method_update_ctx s new_ctx sig ret


end semantics


section cmd_properties
  open TypeDecl
  /-
  - inversion lemmas
  -/

  lemma from_none' : ∀ s0 c s, exec s0 c s → s0 = none → s = none := sorry

  lemma from_none : ∀ c s, exec none c s → s = none := sorry.

  lemma assign_inv: ∀ α d s h (v: Var α) (x: Expr α) s' h' val,
    exec (some (s, h, d)) (v ⇐ x) (some (s', h', d))
    → (eval x s) = some val
    →  h = h' ∧ s' = s.update val v.name := sorry .

  lemma lookup_not_none: ∀ α s h d (v: Var α) (e: Expr (gPtr α)),
    ¬ (exec (some (s, h, d)) (v ↩ e) none)
      → ∃ p, val2loc (eval e s) = some p
        ∧ ∃ (z: Val α), h.lookup p = some z

  lemma mutation_not_none: ∀ α s h d (e: Expr α) (e': Expr (gPtr α)),
   ¬ exec (some (s,h,d)) (e' ≪ e) none
     → ∃ p, val2loc (eval e' s) = some p
      ∧ ∃ (z: Val α), h.lookup p = some z
      ∧ eval e s = some z := sorry

  lemma terminates : ∀ (c : cmd) s, ∃ s', exec (some s) c s' := sorry.

end cmd_properties