import pretty_printing.go_pp

import utils

/-
 - Examples of Go code pretty printing
 -/

open gotype
open goexpr

-- Definitions shared among different tests
def one: goexpr :=
    lit $ literal.intlit 1

def three: goexpr :=
    lit $ literal.intlit 3

def struct1: gotype :=
    structtype [fielddecl.mk "a" inttype, fielddecl.mk "b" booltype]

def emptystruct: gotype :=
    structtype []

def emptyblock: block :=
    block.mk [stmt.sstmt simplestmt.emptystmt]

def justint: list fielddecl :=
    [fielddecl.mk "" inttype]

def err: fielddecl :=
    fielddecl.mk "err" errtype

def intarr: fielddecl :=
    fielddecl.mk  "stream" $ slicetype inttype

def interr: list fielddecl :=
    [fielddecl.mk "n" inttype, err]

def irsig : sig :=
    sig.mk [fielddecl.mk "s" strtype, fielddecl.mk "r" runetype] justint

def indexrune : topdecl :=
    topdecl.fundecl "IndexRune" irsig emptyblock

-- Point example
def pvar : goexpr :=
    named "p"

def sq (x: goexpr): goexpr  :=
    b binop.gomul x x

def pxy2: goexpr :=
    b binop.goadd (sq (sel pvar "x")) (sq (sel pvar "y"))

def ptstruct: gotype :=
    structtype [fielddecl.mk "x" inttype, fielddecl.mk "y" inttype]

def ptlen: topdecl :=
    topdecl.methdecl (fielddecl.mk "p" $ pointertype $ typename "Point")
                     "Length"
                     (sig.mk [] justint)
                     (block.mk [stmt.rstmt [app (named "Math.Sqrt") [pxy2]]])


section Test_pretty_printing

-- LITERALS
-----------

run_cmd test_str "1" one
run_cmd test_str "\"abc\"" $ literal.strlit "abc"

-- DECLARATIONS
---------------

run_cmd test_str "var abc int" $ decl.vardecl "abc" inttype
run_cmd test_str
"func IndexRune(s string, r rune) ( int) {

}"  indexrune

run_cmd test_str
"type Point struct {
    x int
    y int
}" $ topdecl.decl' $ decl.typedecl "Point" ptstruct

-- https://golang.org/ref/spec#Method_declarations
run_cmd test_str
"func (p *Point)Length() ( int) {
return Math.Sqrt(((p.x * p.x) + (p.y * p.y)))
}" ptlen

    --
 run_cmd test_str "const Pi int = 3" $ decl.constdecl "Pi" inttype three

    -- TYPES
    --------

run_cmd test_str
"struct {
}" emptystruct


run_cmd test_str
"struct {
    a int
    b bool
}" struct1

-- https://golang.org/ref/spec#Interface_types
run_cmd test_str
"interface {
    Read(stream []int) (n int, err error)
    Write(stream []int) (n int, err error)
    Close() (err error)
}" $ interfacetype [("Read", sig.mk [intarr] interr),
                    ("Write", sig.mk [intarr] interr),
                    ("Close", sig.mk [] [err])]
-- POINTERS
-----------

run_cmd test_str "*int" $ gotype.pointertype inttype

-- ARRAYS/SLICES
----------------

run_cmd test_str "[1]string" $ arraytype (literal.intlit 1) strtype

run_cmd test_str "[]string" $ slicetype strtype

end Test_pretty_printing