import utils

/-
 - Simplified Go syntax from https://golang.org/ref/spec
 -
 - This is optimized for PRINTING.
 - not for writing Go w/in Lean nor proving things about Lean+Go code.
 -
 - This may not be complete for our purposes, but examples in test_go_pp.lean
 - make this seem basically done, minus some polishing.

 - It's possible we'll need some UserInput format which gets mapped to data
 - structures tailored to proving and to this one for printing.
 -/


inductive Binop_pp
 | goand : Binop_pp
 | goor  : Binop_pp
 | goeq  : Binop_pp
 | gone  : Binop_pp
 | gole  : Binop_pp
 | golt  : Binop_pp
 | goadd : Binop_pp
 | gomul : Binop_pp
 | gosub : Binop_pp


inductive literal : Type
 | intlit : ℤ → literal
 | strlit : string → literal


inductive Unop_pp : Type
 | goneg : Unop_pp
 | gonot : Unop_pp
 | deref : Unop_pp

mutual inductive fielddecl, Gotype, sig

with fielddecl : Type -- component of a structure/interface
 | mk : string → Gotype → fielddecl

with Gotype: Type
 | typename      : string → Gotype
 | booltype      : Gotype
 | inttype       : Gotype
 | strtype       : Gotype
 | runetype      : Gotype
 | errtype       : Gotype
 | arraytype     : literal → Gotype → Gotype -- In reality, length can be Expr
 | structtype    : list fielddecl → Gotype
 | pointertype   : Gotype → Gotype
 | functiontype  : sig → Gotype
 | interfacetype : list (string × sig) → Gotype
 | slicetype     : Gotype → Gotype
 | maptype       : Gotype
 | channeltype   : Gotype

with sig : Type
 | mk: list fielddecl → list fielddecl → sig

mutual inductive decl,
                 forstmt,
                 goexpr,
                 ifstmt,
                 simplestmt,
                 stmt

with decl : Type
 | vardecl   : string → Gotype → decl           -- declaring an inst of a type
 | typedecl  : string → Gotype → decl           -- defining the type
 | constdecl : string → Gotype → goexpr → decl

with forstmt : Type
 | fwhile: goexpr → list stmt → forstmt
 | ffor : simplestmt → goexpr → simplestmt → list stmt → forstmt
 | rfor : string → string → goexpr → list stmt → forstmt

with goexpr : Type
 | un    : Unop_pp → goexpr → goexpr           -- apply (unary) operator
 | bin   : Binop_pp → goexpr → goexpr → goexpr
 | lit   : literal → goexpr
 | conv  : Gotype → goexpr → goexpr         -- type cast
 | sel   : goexpr → string → goexpr         -- apply selector
 | named : string → goexpr                  -- refer to a var, fn, etc. by name
 | app   : goexpr → list goexpr → goexpr    -- apply to arguments

with ifstmt : Type
 | mkb : goexpr → list stmt → list stmt → ifstmt
 | mke : goexpr → list stmt →ifstmt → ifstmt
 | mk  : goexpr → list stmt → ifstmt

with simplestmt : Type
 | emptystmt : simplestmt
 | xstmt: goexpr → simplestmt
 | assignstmt: list goexpr → list goexpr → simplestmt

with stmt : Type
 | dstmt : decl → stmt
 | sstmt : simplestmt → stmt
 | rstmt : list goexpr → stmt
 | bstmt : list stmt → stmt
 | istmt : ifstmt → stmt
 | fstmt : forstmt → stmt

inductive topdecl : Type
 | decl'    : decl → topdecl
 | fundecl  : string → sig → list stmt → topdecl
 | methdecl : fielddecl → string → sig → list stmt → topdecl


structure File: Type := (name: string) (decls: list topdecl)


------------------------------------------------------
open Gotype

-- To-String Implementations


def literal.to_string : literal → string
 | (literal.intlit i) := repr i
 | (literal.strlit i) := repr i

instance : has_to_string literal := ⟨literal.to_string⟩


def Binop_pp.to_string : Binop_pp → string
 | Binop_pp.goand := "&&"
 | Binop_pp.goor  := "||"
 | Binop_pp.goeq  := "=="
 | Binop_pp.gone  := "!="
 | Binop_pp.golt  := "<"
 | Binop_pp.gole  := "<="
 | Binop_pp.goadd := "+"
 | Binop_pp.gosub := "-"
 | Binop_pp.gomul := "*"

instance: has_to_string Binop_pp := ⟨Binop_pp.to_string⟩

def Unop_pp.to_string : Unop_pp → string
 | Unop_pp.goneg := "-"
 | Unop_pp.gonot := "!"
 | Unop_pp.deref := "*"

instance: has_to_string Unop_pp := ⟨Unop_pp.to_string⟩

meta mutual def fielddecl.to_string,
                Gotype.to_string,
                sig.to_string

with fielddecl.to_string : fielddecl → string
 | (fielddecl.mk s t) :=
    s ++ " " ++ t.to_string

with Gotype.to_string : Gotype → string
 | (typename n) := n
 | booltype := "bool"
 | inttype  := "int"
 | strtype  := "string"
 | runetype := "rune"
 | errtype  := "error"
 | (arraytype i t) :=
        "["++i.to_string++"]"++t.to_string
 | (structtype ds) :=
        "struct {" ++ (if ds.length > 0 then "\n    " else "")
            ++ joinstr ds fielddecl.to_string "\n    " ++"\n}"
 | (pointertype t) :=
    "*" ++ t.to_string
 | (functiontype _) := "Function"
 | (interfacetype l) :=
    "interface {"  ++ (if l.length > 0 then "\n    " else "")
         ++ joinstr l (λ⟨a,b⟩, a++b.to_string) "\n    " ++"\n}"
 | (slicetype t) :=
    "[]" ++ t.to_string
 | maptype := "<map>"
 | channeltype := "<chan>"

with sig.to_string : sig → string
 | (sig.mk args ret) :=
    "(" ++ joinstr args fielddecl.to_string ", " ++ ")" ++ " " ++ "("
        ++ joinstr ret fielddecl.to_string ", " ++ ")"

meta instance: has_to_string fielddecl := ⟨fielddecl.to_string⟩

meta instance: has_to_string Gotype := ⟨Gotype.to_string⟩

meta instance: has_to_string sig := ⟨sig.to_string⟩

meta mutual def block,
                decl.to_string,
                forstmt.to_string,
                goexpr.to_string,
                ifstmt.to_string,
                simplestmt.to_string,
                stmt.to_string

with block : list stmt → string
 | xs := "{\n" ++ joinstr xs stmt.to_string "\n\t" ++ "\n}"

with decl.to_string : decl → string
 | (decl.vardecl s t) :=
    "var " ++ s ++ " " ++ t.to_string
 | (decl.constdecl s t e) :=
    "const " ++ s ++ " " ++ t.to_string ++ " = " ++ e.to_string
 | (decl.typedecl s t) :=
    "type " ++ s ++ " " ++ t.to_string

with forstmt.to_string : forstmt → string
 | (forstmt.fwhile c b ) :=
    "for "++c.to_string ++ " " ++ block b
 | (forstmt.ffor inits cond poststmt b) :=
    "for "++inits.to_string ++ "; " ++ cond.to_string ++ "; "
        ++ poststmt.to_string ++ " " ++ block b
 | (forstmt.rfor i s x b) :=
    "for " ++ i ++ ", "++ s ++" := range " ++ x.to_string ++" "++ block b

with goexpr.to_string : goexpr → string
 | (goexpr.bin o x y) :=
    "(" ++ x.to_string ++ " " ++ o.to_string ++ " " ++ y.to_string ++ ")"
 | (goexpr.lit x) :=
    x.to_string
 | (goexpr.conv t x) :=
    t.to_string ++ "("++ x.to_string ++")"
 | (goexpr.un o x) :=
    o.to_string ++ x.to_string
 | (goexpr.sel x n) :=
    x.to_string ++ "." ++ n
 | (goexpr.named n) := n
 | (goexpr.app x args) :=
    x.to_string ++ "("++ joinstr args goexpr.to_string ", " ++ ")"

with ifstmt.to_string : ifstmt → string
 | (ifstmt.mke x b e) :=
    "if "++x.to_string ++ " " ++ block b ++ " else " ++ e.to_string
 | (ifstmt.mkb x b e) :=
    "if " ++ x.to_string ++ " " ++ block b ++ " else " ++ block e
 | (ifstmt.mk x b) :=
    "if " ++ x.to_string ++ " " ++ block b

with simplestmt.to_string : simplestmt → string
 | simplestmt.emptystmt := ""
 | (simplestmt.xstmt x) := x.to_string
 | (simplestmt.assignstmt x y) := joinstr x goexpr.to_string ", "
      ++ " = " ++ joinstr y goexpr.to_string ", "

with stmt.to_string : stmt → string
 | (stmt.dstmt d)  := d.to_string
 | (stmt.sstmt s)  := s.to_string
 | (stmt.rstmt ss) := "return " ++ joinstr ss goexpr.to_string ", "
 | (stmt.bstmt b)  := block b
 | (stmt.istmt i)  := i.to_string
 | (stmt.fstmt i)  := i.to_string


meta instance decldeclts : has_to_string decl :=
   ⟨decl.to_string⟩

meta instance forstmtdeclts : has_to_string forstmt :=
   ⟨forstmt.to_string⟩

meta instance goexprdeclts : has_to_string goexpr :=
   ⟨goexpr.to_string⟩

meta instance ifstmtdeclts : has_to_string ifstmt :=
   ⟨ifstmt.to_string⟩

meta instance simplestmtdeclts : has_to_string simplestmt:=
   ⟨simplestmt.to_string⟩

meta instance stmtdeclts : has_to_string stmt :=
   ⟨stmt.to_string⟩

meta def topdecl.to_string : topdecl → string
 | (topdecl.decl' d) := d.to_string
 | (topdecl.fundecl n s b) :=
    "func " ++ n ++ s.to_string ++ " " ++ block b
 | (topdecl.methdecl t n s b) :=
    "func (" ++ t.to_string ++ ")" ++ n ++ s.to_string ++ " " ++ block b

meta instance: has_to_string topdecl := ⟨topdecl.to_string⟩

meta def File.to_string : File → string
 | ⟨n, ds⟩ := "// generated by Lean Prover pretty printing\n\npackage "
               ++ n ++ "\n\nimport \"errors\"\n\n"
               ++ joinstr ds to_string "\n\n"

meta instance: has_to_string File := ⟨File.to_string⟩

meta def File.write (f: File) (pth: string) :=
   write_file (pth ++ "/" ++ f.name ++ ".go") (to_string f)

