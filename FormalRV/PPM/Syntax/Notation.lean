/-
  FormalRV.PPM.Syntax.Notation
  ────────────────────────────
  Human-readable notation for PPM programs (John's syntax) + a pretty-printer.
  A program is DECLARED as such once — the instructions inside are bare:

      ppm_program tTeleport {
        useT[1];
        c0 = Measure Z[0]Z[1];
        if c0 == 1 then X[1] else skip
      }

  This elaborates to `def tTeleport : PPMProg := [...]` — a plain syntax tree
  (`Program.lean`), so everything downstream (well-formedness, semantics, the
  `Resource/` counters) works on ordinary data; the notation is a paper-thin
  surface, never load-bearing.  Parity conditions: `if c0 ^^ c2 == 1 then …`.
  (A term-level form `ppm! { … }` also exists for inline use in theorems.)
-/
import FormalRV.PPM.Syntax.Program

namespace FormalRV.PPM.Prog

open Lean

/-! ## §1. Syntax categories. -/

declare_syntax_cat ppmFactor
syntax "X[" num "]" : ppmFactor
syntax "Y[" num "]" : ppmFactor
syntax "Z[" num "]" : ppmFactor

declare_syntax_cat ppmStmt
syntax ident " = " "Measure" ppmFactor+ : ppmStmt
syntax "frame" ppmFactor+ : ppmStmt
syntax "if" ident ("^^" ident)* "==" num "then" ppmFactor+ "else" "skip" : ppmStmt
syntax "if" ident ("^^" ident)* "==" num "then" ppmFactor+ "else" ppmFactor+ : ppmStmt
syntax "useT" "[" num "]" : ppmStmt
syntax "useCCZ" "[" num "," num "," num "]" : ppmStmt

syntax "ppm!" "{" sepBy(ppmStmt, ";") "}" : term

/-! ## §2. Elaboration to the `PPMProg` data. -/

/-- Outcome identifiers must be `c<index>` (`c0`, `c1`, …). -/
private def cvarLit (id : Syntax) : MacroM (TSyntax `term) := do
  let s := id.getId.toString
  if s.startsWith "c" then
    match (s.drop 1).toNat? with
    | some n => return Syntax.mkNumLit (toString n)
    | none => Macro.throwErrorAt id "outcome variable must be c<index> (e.g. c2)"
  else
    Macro.throwErrorAt id "outcome variable must be c<index> (e.g. c2)"

private def factorTerm : TSyntax `ppmFactor → MacroM (TSyntax `term)
  | `(ppmFactor| X[$n]) => `(PFactor.mk $n PKind.x)
  | `(ppmFactor| Y[$n]) => `(PFactor.mk $n PKind.y)
  | `(ppmFactor| Z[$n]) => `(PFactor.mk $n PKind.z)
  | _ => Macro.throwError "unsupported Pauli factor"

private def productTerm (fs : Array (TSyntax `ppmFactor)) : MacroM (TSyntax `term) := do
  let ts ← fs.mapM factorTerm
  `([$ts,*])

private def parityTerm (ids : Array Syntax) : MacroM (TSyntax `term) := do
  let ts ← ids.mapM cvarLit
  `([$ts,*])

private def stmtTerm : TSyntax `ppmStmt → MacroM (TSyntax `term)
  | `(ppmStmt| $c:ident = Measure $fs:ppmFactor*) => do
      let dst ← cvarLit c
      let P ← productTerm fs
      `(PPMStmt.measure $dst $P)
  | `(ppmStmt| frame $fs:ppmFactor*) => do
      let P ← productTerm fs
      `(PPMStmt.frame $P)
  | `(ppmStmt| if $c0:ident $[^^ $cs:ident]* == $one:num then $thn:ppmFactor* else skip) => do
      unless one.getNat == 1 do Macro.throwErrorAt one "corrections fire on parity == 1"
      let par ← parityTerm (#[c0] ++ cs : Array Syntax)
      let T ← productTerm thn
      `(PPMStmt.correct $par $T [])
  | `(ppmStmt| if $c0:ident $[^^ $cs:ident]* == $one:num then $thn:ppmFactor* else $els:ppmFactor*) => do
      unless one.getNat == 1 do Macro.throwErrorAt one "corrections fire on parity == 1"
      let par ← parityTerm (#[c0] ++ cs : Array Syntax)
      let T ← productTerm thn
      let E ← productTerm els
      `(PPMStmt.correct $par $T $E)
  | `(ppmStmt| useT[$q]) => `(PPMStmt.useT $q)
  | `(ppmStmt| useCCZ[$a, $b, $c]) => `(PPMStmt.useCCZ $a $b $c)
  | _ => Macro.throwError "unsupported PPM statement"

macro_rules
  | `(ppm! { $[$stmts];* }) => do
      let ts ← stmts.mapM stmtTerm
      `(([$ts,*] : PPMProg))

/-- **The program-declaration command** — declare a named PPM program with bare
instructions (the declaration announces "PPM" once; no per-block prefix):
`ppm_program foo { c0 = Measure X[0]Z[1]; if c0 == 1 then X[1] else skip }`. -/
syntax "ppm_program " ident " {" sepBy(ppmStmt, ";") "}" : command

macro_rules
  | `(ppm_program $name:ident { $[$stmts];* }) => do
      let ts ← stmts.mapM stmtTerm
      `(def $name : PPMProg := [$ts,*])

/-! ## §3. Pretty-printer (round-trip display). -/

def PKind.render : PKind → String
  | .x => "X" | .y => "Y" | .z => "Z"

def PFactor.render (f : PFactor) : String := s!"{f.kind.render}[{f.qubit}]"

def PauliProduct.render (P : PauliProduct) : String :=
  String.join (P.map PFactor.render)

def renderParity : List CVar → String
  | []      => ""
  | [c]     => s!"c{c}"
  | c :: cs => s!"c{c} ^^ " ++ renderParity cs

def PPMStmt.render : PPMStmt → String
  | .measure dst P     => s!"c{dst} = Measure {P.render}"
  | .measureSel sel dst Pt Pe =>
      s!"c{dst} = MeasureIf {renderParity sel} then {Pt.render} else {Pe.render}"
  | .measureSel2 sel1 sel2 dst P00 P01 P10 P11 =>
      s!"c{dst} = MeasureSel2 ({renderParity sel1}; {renderParity sel2}) "
        ++ s!"{P00.render} {P01.render} {P10.render} {P11.render}"
  | .frame P           => s!"frame {P.render}"
  | .correct par thn els =>
      let e := if els.isEmpty then "skip" else els.render
      s!"if {renderParity par} == 1 then {thn.render} else {e}"
  | .correctQ mons thn els =>
      let e := if els.isEmpty then "skip" else els.render
      let ms := String.intercalate " ^^ "
        (mons.map (fun mon => String.intercalate "*" (mon.map (s!"c{·}"))))
      s!"if {ms} == 1 then {thn.render} else {e}"
  | .useT q            => s!"useT[{q}]"
  | .useCCZ a b c      => s!"useCCZ[{a},{b},{c}]"

def PPMProg.render (p : PPMProg) : String :=
  String.intercalate ";\n" (p.map PPMStmt.render)

/-! ## §4. Smoke checks: the notation elaborates to exactly the data tree. -/

example :
    (ppm! { c0 = Measure X[0]Z[1]X[3] })
      = [PPMStmt.measure 0 [⟨0, .x⟩, ⟨1, .z⟩, ⟨3, .x⟩]] := rfl

example :
    (ppm! { c0 = Measure Z[0]Z[1];
            if c0 == 1 then X[1] else skip })
      = [PPMStmt.measure 0 [⟨0, .z⟩, ⟨1, .z⟩],
         PPMStmt.correct [0] [⟨1, .x⟩] []] := rfl

example :
    (ppm! { c0 = Measure X[0]X[1];
            c1 = Measure Z[1]Z[2];
            if c0 ^^ c1 == 1 then Z[0] else X[2];
            useT[2] })
      = [PPMStmt.measure 0 [⟨0, .x⟩, ⟨1, .x⟩],
         PPMStmt.measure 1 [⟨1, .z⟩, ⟨2, .z⟩],
         PPMStmt.correct [0, 1] [⟨0, .z⟩] [⟨2, .x⟩],
         PPMStmt.useT 2] := rfl

/-! The worked T-teleport-shaped program (semantic retrofit is Phase C),
declared with bare instructions via `ppm_program`. -/
ppm_program tTeleportSkeleton {
  useT[1];
  c0 = Measure Z[0]Z[1];
  if c0 == 1 then X[1] else skip
}

example : tTeleportSkeleton.wf = true := by decide
example : tTeleportSkeleton.width = 2 := by decide
example : tTeleportSkeleton.cwidth = 1 := by decide

end FormalRV.PPM.Prog
