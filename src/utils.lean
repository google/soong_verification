import system.io
import data.option.basic
import data.list.alist   -- association lists
import data.finmap
import data.finset.sort
/-
 - Any basic utility functions used around the project can go here
 -/

section strings
  /-
   - Write a given string to a given path
   - e.g. #eval write_file "/tmp/test.txt" "abcd"
   -/
  def write_file (fname: string) (txt: string): io unit := do
    h <- io.mk_file_handle fname io.mode.write,
    io.fs.write h txt.to_char_buffer

  /-
   - Display a value of a printable type
   -/
  meta def render {α:Type*} [has_to_string α] (x: α): io unit :=
    io.put_str (to_string x) -- formats (e.g. \n\t) the output of "to_string"

  /-
   - Join list of printable things with optional delimiter:
   - E.g. join ["ab", "c"] = "abc"     ...   join ["x", "y"] "," = "x,y"
   -/
  def joinstr {α:Type} (lst : list α) (printFun : α → string)
                            (delim : string := "") : string :=
      string.join ((lst.map printFun).intersperse delim)


  /-
   - Throw error if expected equality does not hold
   -/
  meta def test{α : Type*} [decidable_eq α] (a b: α):
    tactic unit := guard $ a = b

  meta def test_not{α : Type*} [decidable_eq α] (a b: α):
    tactic unit := guard $ ¬ a = b

  meta def test_str {α : Type*} [has_to_string α] (b : string) (a : α)
                                : tactic unit :=
  guard $ to_string a = b

end strings

section maps

  def show_finmap {α β: Type} {γ: β → Type} [decidable_eq α]
    [has_to_string α] [linear_order α] [has_to_string β] [∀ b:β, has_to_string (γ b)]
    [decidable_rel (λ (x y : α), x ≤ y)] (a: finmap (λ _:α, Σ s: β, γ s)) :=
      if a.keys.card = 0 then "" else
      " - " ++ joinstr (a.keys.sort (λ x y, x <= y)) (λ x:α, to_string x ++ ": "
        ++ match a.lookup x with
         | none := ""
         | some ⟨y, z⟩:= to_string z ++ " (" ++ to_string y ++")"
         end ) "\n - "


  def show_alist {α β: Type} {γ: β → Type}
    [has_to_string α] [has_to_string β] [∀ b:β, has_to_string (γ b)]
    (a: alist (λ _:α, Σ s: β, γ s)) :=
      " - " ++ joinstr a.entries (λ⟨x,y,z⟩, to_string x ++ ": " ++
      to_string z ++ " (" ++ to_string y ++")") "\n - "

  /-
   - Association lists can be seen as lists of triples (key, type_index, val)
   - where the type of key and type_index are fixed, and the value of val is
   - of a type that is determined by the value of type_index. Keys are unique.
   -
   - But sometimes we just want a list of pairs (no *dependent* types)
   - where the first value is unique, so this defines an alist where the
   - "type_index" value is just a dummy (unit type).
   -/
  abbreviation pairmap (α β: Type*) := alist (λ _: α, Σ _: unit, β)

  /-
   - Creates a pairmap from a list of pairs (first value has priority if there
   - are duplicate keys)..
   -/
  def to_pairmap_first_unique: Π{α β: Type*} [decidable_eq α],
                               list (α × β) → pairmap α β
    | α β d []         := @list.to_alist α d (λ _: α, Σ _: unit, β) []
    | α β d ((a,b)::t) := @alist.insert α (λ _: α, Σ _: unit, β)
                              d a ⟨(), b⟩
                              (@to_pairmap_first_unique α β d t)

  /-
   - Convert a pairmap back to a list of pairs
   -/
  def from_pairmap_recursive : Π {α β : Type*},
     list (Σ (_x : α) (_x : unit), β) → list (α × β)
   | _ _ []               := []
   | _ _ (⟨a, ⟨_, b⟩⟩::t) := (a,b) :: from_pairmap_recursive t

  def from_pairmap  {α β : Type*} (m: pairmap α β): list (α × β) :=
    from_pairmap_recursive m.entries

  def pairmap.map {α β γ: Type*} (m: pairmap α β) (f: (α × β) → γ): list γ
    := (from_pairmap m).map f

  /-
   - Simplified lookup for pairmaps
   -/
  def plookup {α β : Type*} [decidable_eq α]
              (m: pairmap α β) (key: α) : option β :=
      option.elim (m.lookup key) none (λ ⟨_, b⟩, some b)

  /-
   - Printing a pairlist
   -/
  def str_pair : Π{α β: Type*} [has_to_string α] [has_to_string β],
                                (α×β) → string
   |  α β ha hb ab :=  @to_string α ha ab.1 ++", "  ++
                       @to_string β hb ab.2

  def str_pairlist : Π{α β: Type*} [has_to_string α] [has_to_string β],
                      list (α×β) → string
   | _ _ _  _  []     :=  ""
   | α β ha hb (ab::t) :=  @str_pair α β ha hb ab ++ "\n"
                           ++ @str_pairlist α β ha hb t

  instance: Π{α β: Type*} [has_to_string α] [has_to_string β],
                          has_to_string (pairmap α β)
    | α β ha hb := ⟨λ x, @str_pairlist α β ha hb (from_pairmap x)⟩

end maps