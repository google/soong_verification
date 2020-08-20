import seplog.b_memory
import data.list.basic

section exprs

  open TypeDecl open Val

  @[derive decidable_eq]
  structure Var (t: TypeDecl) := (name: string)

  @[derive decidable_eq]
  inductive Expr: TypeDecl → Type
   | const  {α: TypeDecl}: Val α → Expr α
   | getvar {α: TypeDecl}: Var α → Expr α
   | relop {α: TypeDecl}:
      Relop → Expr α → Expr α → Expr gBool
   | binop {α: TypeDecl}:
      Binop → Expr α → Expr α → Expr α
   | unop {α: TypeDecl}:
      Unop → Expr α → Expr α
  | get_field {struct: string} {α: TypeDecl}:
      Expr (gRef struct) → string → Expr α
  | update_field {struct: string} {α: TypeDecl}: -- pure update/not mutation
      Expr (gRef struct) → string → Expr α → Expr (gRef struct)

	notation x ` ↠ ` e : 50 := (Expr.get_field x e)
	notation a ` ⋀ ` b : 50 := (Expr.binop Binop.AND a b)
	notation a ` ⋁ ` b : 50 := (Expr.binop Binop.OR a b)
	notation a ` ≃ ` b : 50 := (Expr.relop Relop.EQ a b)
	notation a ` ≢ ` b : 50 := (Expr.relop Relop.NEQ a b)
  notation  ` ¡ ` :50 := Expr.unop Unop.NOT
  def Expr.gotype {α: TypeDecl} (x: Expr α):  TypeDecl := α

  def Var.gotype {α: TypeDecl} (x: Var α): TypeDecl := α

  def goFalse: Expr gBool := Expr.const $ pBool ff
  def goTrue:  Expr gBool := Expr.const $ pBool tt
  def goZero:  Expr gInt  := Expr.const $ pInt 0
  def goOne:   Expr gInt  := Expr.const $ pInt 1
  def goEmpty: Expr gStr  := Expr.const $ pStr ""
  def goNil {t}: Expr (gPtr t) := Expr.const $ pPtr _ none
  def isEmpty: Expr gStr → Expr gBool := Expr.relop Relop.EQ goEmpty
  def isNil {t}: Expr (gPtr t) → Expr gBool := Expr.relop Relop.EQ goNil

  /-
   - Access a the environment with a variable (possibly fails via "none")
   - Fails if the name-type pair is not found
   -/
  @[simp] def get_var: Π{α:TypeDecl} ,
                        Var α → Store → option (Val α)
    | α  ⟨key⟩  ⟨e⟩ :=
      match e.lookup key with
       | none := none
       | (some ⟨_,  val⟩) := as_type val α
      end

end exprs

section cmds

  open TypeDecl

  @[derive decidable_eq]
  inductive cmd: Type
    | skip: cmd
    | assign   {α}: Var α         → Expr α        → cmd
    | lookup   {α}: Var α         → Expr (gPtr α) → cmd
    | mutation {α}: Expr (gPtr α) → Expr α        → cmd
    | while:        Expr gBool    → cmd           → cmd
    | seq:          cmd           → cmd           → cmd
    | ifte:         Expr gBool    → cmd           → cmd → cmd
    | declare  {α}: Var α         → cmd
    | new  {α}: Var (gPtr α)  → cmd
    | call {struct: string}
           -- object whose method is called (either an obj or a pointer to it)
           (callee: Expr (gPtr (gRef struct)) ⊕ Expr (gRef struct))
           (method: string)             -- Name of method
           (arg: list (Σ α, Expr α))    -- Values we want to pass to the func
           (res: list (Σ α, Var α))    -- store results in these variables
           : cmd.

    -- These may be needed at some point
    -- | malloc   {α: TypeDecl}: Var (gPtr α)  → Expr α        → cmd
    -- | free     {α: TypeDecl}: Expr (gPtr α) → cmd


	notation x ` ⇐ ` e : 80 := (cmd.assign   x e) -- <-
  notation x ` ↩ ` e : 80 := (cmd.lookup   x e) -- <-*
  notation x ` ≪ ` e : 80 := (cmd.mutation x e) -- *<-
  notation x ` ∣ ` : 81 e := (cmd.seq x e) -- ;
  -- notation x ` ◃ ` e : 80 := (cmd.malloc x e) -- <--malloc
  open cmd

  @[simp]
  def cmd.ift (b: Expr gBool) (c: cmd): cmd := ifte b c skip

  @[simp]
  def cmd.dassign {α} (b: Var α) (c: Expr α): cmd := (declare b) ∣ (assign b c)

  notation x ` :≃ ` : 81 e := (cmd.dassign x e) -- ;

  @[simp]
  def cmd.ifs (pairs: list (Expr gBool × cmd)) (other: cmd): cmd :=
    pairs.foldr (λ⟨i,t⟩ e, ifte i t e) skip

end cmds

