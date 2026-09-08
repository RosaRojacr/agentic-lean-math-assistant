/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneLocalInterval

/-!
# Data-only signed-integer traces for the source-native scalar checker

Concrete traces contain only operation tags, backward references, and signed
integer endpoints at the fixed scale `2^160`.  Acceptance performs no rational
normalization and constructs no real expression or proof-bearing interval jet.
The real soundness boundary is supplied once in this module.
-/

namespace NearOneScalarInteger

open Real

/-- Fixed denominator used by the retained 160-bit outward arithmetic. -/
def scale : Int :=
  1461501637330902918203684832716283019655932542976

@[simp] theorem scale_eq : scale = (2 : Int) ^ 160 := by norm_num [scale]

/-- A proof-free closed dyadic interval. -/
structure Interval where
  lo : Int
  hi : Int
  deriving DecidableEq, Repr

namespace Interval

/-- Real interpretation; this is absent from concrete acceptance computation. -/
def RealContains (i : Interval) (x : ℝ) : Prop :=
  ((i.lo : ℝ) / (scale : ℝ)) ≤ x ∧ x ≤ ((i.hi : ℝ) / (scale : ℝ))

/-- Exact-rational interpretation used only by shared soundness proofs. -/
def toQInterval (i : Interval) (h : i.lo ≤ i.hi) :
    LeanSuffixReflective.QInterval where
  lo := (i.lo : ℚ) / (scale : ℚ)
  hi := (i.hi : ℚ) / (scale : ℚ)
  ordered := by
    apply div_le_div_of_nonneg_right
    · exact_mod_cast h
    · norm_num [scale]

@[simp] theorem toQInterval_realContains (i : Interval) (h : i.lo ≤ i.hi)
    (x : ℝ) : (i.toQInterval h).RealContains x ↔ i.RealContains x := by
  simp [toQInterval, RealContains, LeanSuffixReflective.QInterval.RealContains]

end Interval

inductive InputMode
  | point
  | range
  deriving DecidableEq, Repr

inductive DomainKind
  | foldLower
  | foldUpper
  | areaLower
  | areaUpper
  | whole
  deriving DecidableEq, Repr

inductive Sign
  | positive
  | negative
  deriving DecidableEq, Repr

/-- Data-bearing operation. Inputs retain exact rational endpoints solely as
integer numerator/positive-denominator pairs checked by cross multiplication. -/
inductive Op
  | input (slot : Nat) (mode : InputMode)
      (loNum : Int) (loDen : Nat) (hiNum : Int) (hiDen : Nat)
  | rat (num : Int) (den : Nat)
  | pi
  | add (a b : Nat)
  | neg (a : Nat)
  | mul (a b : Nat)
  | pow (a exponent : Nat)
  | recip (a : Nat)
  | sqrt (a : Nat)
  | tailValue (a index terms : Nat)
  | tailDerivative (a index terms : Nat)
  | intersect (a b : Nat)
  deriving DecidableEq, Repr

/-- Numeric payload erased from inputs. This fixed schedule prevents a cell
certificate from replacing the source program or changing a domain mask. -/
inductive OpShape
  | input (slot : Nat) (mode : InputMode)
  | rat (num : Int) (den : Nat)
  | pi
  | add (a b : Nat)
  | neg (a : Nat)
  | mul (a b : Nat)
  | pow (a exponent : Nat)
  | recip (a : Nat)
  | sqrt (a : Nat)
  | tailValue (a index terms : Nat)
  | tailDerivative (a index terms : Nat)
  | intersect (a b : Nat)
  deriving DecidableEq, Repr

namespace Op

def shape : Op → OpShape
  | .input slot mode _ _ _ _ => .input slot mode
  | .rat num den => .rat num den
  | .pi => .pi
  | .add a b => .add a b
  | .neg a => .neg a
  | .mul a b => .mul a b
  | .pow a n => .pow a n
  | .recip a => .recip a
  | .sqrt a => .sqrt a
  | .tailValue a k n => .tailValue a k n
  | .tailDerivative a k n => .tailDerivative a k n
  | .intersect a b => .intersect a b

end Op

structure Step where
  op : Op
  out : Interval
  deriving DecidableEq, Repr

structure OutputBinding where
  ref : Nat
  sign : Sign
  deriving DecidableEq, Repr

structure Program where
  shapes : Array OpShape
  outputs : Array OutputBinding

structure Trace where
  kind : DomainKind
  steps : Array Step

private def ordered (i : Interval) : Bool := decide (i.lo ≤ i.hi)

private def rationalPointValid (out : Interval) (num : Int) (den : Nat) : Bool :=
  decide (0 < den) && ordered out &&
    decide (out.lo * (den : Int) ≤ num * scale) &&
    decide (num * scale ≤ out.hi * (den : Int))

private def rationalRangeValid (out : Interval)
    (loNum : Int) (loDen : Nat) (hiNum : Int) (hiDen : Nat) : Bool :=
  decide (0 < loDen) && decide (0 < hiDen) && ordered out &&
    decide (loNum * (hiDen : Int) ≤ hiNum * (loDen : Int)) &&
    decide (out.lo * (loDen : Int) ≤ loNum * scale) &&
    decide (hiNum * scale ≤ out.hi * (hiDen : Int))

private def addValid (out a b : Interval) : Bool :=
  ordered out && decide (out.lo ≤ a.lo + b.lo) && decide (a.hi + b.hi ≤ out.hi)

private def negValid (out a : Interval) : Bool :=
  ordered out && decide (out.lo ≤ -a.hi) && decide (-a.lo ≤ out.hi)

private def mulValid (out a b : Interval) : Bool :=
  let products := #[a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi]
  ordered out && products.all (fun p =>
    decide (out.lo * scale ≤ p) && decide (p ≤ out.hi * scale))

private def powValid (out a : Interval) (n : Nat) : Bool :=
  if n = 0 then
    ordered out && decide (out.lo ≤ scale) && decide (scale ≤ out.hi)
  else
    let factor := scale ^ (n - 1)
    let lowerUpper :=
      if n % 2 = 1 then
        decide (out.lo * factor ≤ a.lo ^ n) &&
          decide (a.hi ^ n ≤ out.hi * factor)
      else if 0 ≤ a.lo then
        decide (out.lo * factor ≤ a.lo ^ n) &&
          decide (a.hi ^ n ≤ out.hi * factor)
      else if a.hi ≤ 0 then
        decide (out.lo * factor ≤ a.hi ^ n) &&
          decide (a.lo ^ n ≤ out.hi * factor)
      else
        decide (out.lo ≤ 0) &&
          decide (a.lo ^ n ≤ out.hi * factor) &&
          decide (a.hi ^ n ≤ out.hi * factor)
    ordered out && lowerUpper

private def recipValid (out a : Interval) : Bool :=
  ordered out && decide (0 < a.lo) && decide (0 < out.lo) &&
    decide (out.lo * a.hi ≤ scale * scale) &&
    decide (scale * scale ≤ out.hi * a.lo)

private def sqrtValid (out a : Interval) : Bool :=
  ordered out && decide (0 < out.lo) &&
    decide (out.lo * out.lo ≤ scale * a.lo) &&
    decide (scale * a.hi ≤ out.hi * out.hi)

private def tailValueValid (out a : Interval) (index terms : Nat) : Bool :=
  let m : Int := Int.ofNat (max a.lo.natAbs a.hi.natAbs)
  let exponent := 2 * terms
  let den : Int := Int.ofNat (2 * (index + terms) + 1)
  ordered out && decide (0 ≤ out.hi) && decide (out.lo = -out.hi) &&
    decide (2 * m ≤ scale) &&
    decide (m ^ exponent ≤ out.hi * scale ^ (exponent - 1) * den)

private def tailDerivativeValid (out a : Interval) (index terms : Nat) : Bool :=
  let m : Int := Int.ofNat (max a.lo.natAbs a.hi.natAbs)
  let exponent := 2 * terms
  let den : Int := Int.ofNat (2 * (index + terms) + 1)
  let denNext : Int := den + 2
  ordered out && decide (0 < terms) && decide (0 ≤ out.hi) &&
    decide (out.lo = -out.hi) && decide (2 * m ≤ scale) &&
    decide ((2 * (terms : Int)) * m ^ (exponent - 1) * scale ^ 2 * denNext +
        2 * m ^ (exponent + 1) * den ≤
      out.hi * scale ^ exponent * den * denNext)

private def intersectValid (out a b : Interval) : Bool :=
  ordered out && decide (out.lo = max a.lo b.lo) &&
    decide (out.hi = min a.hi b.hi)

private def withOne (env : Array Interval) (a : Nat)
    (f : Interval → Bool) : Bool :=
  match env[a]? with
  | some x => f x
  | none => false

private def withTwo (env : Array Interval) (a b : Nat)
    (f : Interval → Interval → Bool) : Bool :=
  match env[a]?, env[b]? with
  | some x, some y => f x y
  | _, _ => false

/-- One fail-closed arithmetic step. Every reference must point backward. -/
def checkStep (env : Array Interval) (step : Step) : Bool :=
  match step.op with
  | .input _ mode loNum loDen hiNum hiDen =>
      rationalRangeValid step.out loNum loDen hiNum hiDen &&
        match mode with
        | .point => decide (loNum * (hiDen : Int) = hiNum * (loDen : Int))
        | .range => true
  | .rat num den => rationalPointValid step.out num den
  | .pi =>
      decide (step.out.lo = 4591442807048218921384805199743311128454155024418) &&
      decide (step.out.hi = 4591442807048218921384805199743311128454155024419)
  | .add a b => withTwo env a b (addValid step.out)
  | .neg a => withOne env a (negValid step.out)
  | .mul a b => withTwo env a b (mulValid step.out)
  | .pow a n => withOne env a (fun x => powValid step.out x n)
  | .recip a => withOne env a (recipValid step.out)
  | .sqrt a => withOne env a (sqrtValid step.out)
  | .tailValue a k n => withOne env a (fun x => tailValueValid step.out x k n)
  | .tailDerivative a k n =>
      withOne env a (fun x => tailDerivativeValid step.out x k n)
  | .intersect a b => withTwo env a b (intersectValid step.out)

/-- Run one flat trace. The array is the checked environment of node outputs. -/
def run (steps : Array Step) : Option (Array Interval) := Id.run do
  let mut env := #[]
  for step in steps do
    if !checkStep env step then return none
    env := env.push step.out
  return some env

private def outputValid (env : Array Interval) (binding : OutputBinding) : Bool :=
  match env[binding.ref]? with
  | none => false
  | some out =>
      match binding.sign with
      | .positive => decide (0 < out.lo)
      | .negative => decide (out.hi < 0)

/-- Acceptance fixes the complete operation schedule and every final sign slot. -/
def acceptTrace (program : Program) (trace : Trace) : Bool :=
  trace.steps.map (fun step => step.op.shape) == program.shapes &&
    match run trace.steps with
    | none => false
    | some env => program.outputs.all (outputValid env)

/-- Exactly the five frozen face/whole-box domain packages. -/
def acceptCell (program : DomainKind → Program) (traces : Array Trace) : Bool :=
  match traces[0]?, traces[1]?, traces[2]?, traces[3]?, traces[4]? with
  | some a, some b, some c, some d, some e =>
      decide (traces.size = 5) && decide (a.kind = .foldLower) &&
      decide (b.kind = .foldUpper) && decide (c.kind = .areaLower) &&
      decide (d.kind = .areaUpper) && decide (e.kind = .whole) &&
      acceptTrace (program a.kind) a && acceptTrace (program b.kind) b &&
      acceptTrace (program c.kind) c && acceptTrace (program d.kind) d &&
      acceptTrace (program e.kind) e
  | _, _, _, _, _ => false

/-! ## Basic integer-to-real soundness boundary -/

private theorem scale_pos : (0 : Int) < scale := by norm_num [scale]

/-- A checked rational leaf is enclosed after interpretation in the reals. -/
theorem rationalPoint_sound {out : Interval} {num : Int} {den : Nat}
    (hden : 0 < den)
    (hlo : out.lo * (den : Int) ≤ num * scale)
    (hhi : num * scale ≤ out.hi * (den : Int)) :
    out.RealContains ((num : ℝ) / (den : ℝ)) := by
  have hsR : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast scale_pos
  have hdR : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  have hloR : (out.lo : ℝ) * (den : ℝ) ≤ (num : ℝ) * (scale : ℝ) := by
    exact_mod_cast hlo
  have hhiR : (num : ℝ) * (scale : ℝ) ≤ (out.hi : ℝ) * (den : ℝ) := by
    exact_mod_cast hhi
  constructor
  · exact (div_le_div_iff₀ hsR hdR).2 hloR
  · exact (div_le_div_iff₀ hdR hsR).2 hhiR

/-- Integer endpoint addition checks compose semantically. -/
theorem add_sound {out a b : Interval}
    (hout : out.lo ≤ a.lo + b.lo ∧ a.hi + b.hi ≤ out.hi)
    {x y : ℝ} (hx : a.RealContains x) (hy : b.RealContains y) :
    out.RealContains (x + y) := by
  rcases hx with ⟨hxl, hxu⟩
  rcases hy with ⟨hyl, hyu⟩
  have hsR : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast scale_pos
  constructor
  · have hcast : (out.lo : ℝ) ≤ (a.lo : ℝ) + (b.lo : ℝ) := by
      exact_mod_cast hout.1
    have hscaled := div_le_div_of_nonneg_right hcast hsR.le
    have hsum := add_le_add hxl hyl
    rw [← add_div] at hsum
    exact hscaled.trans hsum
  · have hcast : (a.hi : ℝ) + (b.hi : ℝ) ≤ (out.hi : ℝ) := by
      exact_mod_cast hout.2
    have hscaled := div_le_div_of_nonneg_right hcast hsR.le
    have hsum := add_le_add hxu hyu
    rw [← add_div] at hsum
    exact hsum.trans hscaled


end NearOneScalarInteger
