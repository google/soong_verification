import pretty_printing.go_pp
import seplog.d_context

/-
 - Pretty printing.
 -/

open decl open topdecl open Gotype open TypeDecl open Val
open cmd open simplestmt open stmt open literal open goexpr
open Expr open Binop open Relop open Binop_pp open Unop_pp
open ifstmt open forstmt

def td_to_gt: TypeDecl → Gotype
 | gInt       := inttype
 | gStr       := strtype
 | gErr       := errtype
 | gBool      := booltype
 | (gArr n t) := arraytype (intlit n) (td_to_gt t)
 | (gRef s)   := typename s
 | (gPtr t)   := pointertype $ td_to_gt t

def pair_to_fielddecl: (string × TypeDecl) → fielddecl
 | (s, p) := fielddecl.mk s $ td_to_gt p

def to_binop: Binop → Binop_pp
 | OR    := goor
 | PLUS  := goadd
 | MINUS := gosub
 | AND   := goand

def to_relop: Relop → Binop_pp
 | EQ  := goeq
 | NEQ := gone
 | LEQ := gole

def to_unop: Unop → Unop_pp
 | NOT := gonot

def var_to_expr {α} (v: Var α): goexpr := named v.name

def to_expr: Π{α: TypeDecl}, Expr α → goexpr
 | _ (getvar v)    := var_to_expr v
 | _ (binop o x y) := bin (to_binop o) (to_expr x) (to_expr y)
 | _ (relop o x y) := bin (to_relop o) (to_expr x) (to_expr y)
 | _ (unop o x)    := un (to_unop o) (to_expr x)

 | gInt       (const (pInt x))   := lit $ intlit x
 | gStr       (const x)          := lit $ strlit x.sval
 | (gArr _ _) (const x)          := named "Const array NOT IMPLEMENTED"
 | (gRef _)   (const x)          := named "Const struct NOT IMPLEMENTED"
 | gBool      (const (pBool x))  := named (if x then "true" else "false")
 | (gPtr x)   (const (pPtr _ y)) := y.elim (named "nil") (λ i, lit $ intlit i)
 | gErr       (const (pErr x))   := app (sel (named "errors") "New")
                                        [lit $ strlit x]

 | (gRef _)  (update_field x _ _) := named "update field NOT IMPLEMENTED"

 | (gRef _) (get_field x f) := sel (to_expr x) f

meta mutual def cmd_to_stmts, to_if
with cmd_to_stmts: cmd → list stmt
 | skip             := []
 | (cmd.assign a z) := [sstmt $ assignstmt [named a.name] [to_expr z]]
 | (seq a b)        := cmd_to_stmts a ++ cmd_to_stmts b
 | (ifte a b c)     := [istmt $ to_if (ifte a b c)]
 | (mutation a b)   := [sstmt $ assignstmt [un deref $ to_expr a] [to_expr b]]
 | (while a b)      := [fstmt $ fwhile (to_expr a) (cmd_to_stmts b)]
 | (@new α b)       := [dstmt $ vardecl b.name (td_to_gt α)]
 | (@declare α b)   := [dstmt $ vardecl b.name (td_to_gt α)]
 | (lookup a b)     := [sstmt $ assignstmt [var_to_expr a]
                                [un deref $ to_expr b]]
 | (call a b c d)   := [sstmt $
    assignstmt (d.map (λ (z:Σ α, Var α), var_to_expr z.2))
    [app (sel (a.elim to_expr to_expr) b)
        $ c.map (λ (z:Σ α, Expr α), to_expr z.2)]]

/-
 - Make if statements more pretty rather than treating everything as ifThenElse
 -/
with to_if: cmd → ifstmt
 | (ifte a b skip) := ifstmt.mk (to_expr a) ( cmd_to_stmts b)

 | (ifte a b (ifte c d e)) := mke (to_expr a) ( cmd_to_stmts b)
                              (to_if (ifte c d e))
 | (ifte a b c) :=  mkb (to_expr a) ( cmd_to_stmts b)
                                    ( cmd_to_stmts c)
 | _ := ifstmt.mk (named "")  []

def struct_typedecl (s: string) (fields: list (string × TypeDecl)): topdecl :=
  decl' $ typedecl s $ structtype $ fields.map pair_to_fielddecl

meta def meth_decl (str: string) (m: string) (s: Sig) (c: cmd): topdecl :=
  methdecl
    (fielddecl.mk s.receiver $ (if s.is_ptr then pointertype else id)
                             $ typename str)
    m (sig.mk (s.args.map pair_to_fielddecl) (s.return.map pair_to_fielddecl))
      (cmd_to_stmts c ++ [rstmt []])

meta def struct_to_topdecl {n} (s: GoStructDecl n): list topdecl :=
  match s with
   | ⟨fields, methods⟩ := [struct_typedecl n $ from_pairmap fields]
    ++ (methods.map  (λ ⟨x,y,z⟩, meth_decl n x y z))
  end

meta def structs_to_file (name: string) (structs: list (Σ s, GoStructDecl s))
                    : File :=
  ⟨name, list.join $ structs.map (λ ⟨_,b⟩, struct_to_topdecl b)⟩