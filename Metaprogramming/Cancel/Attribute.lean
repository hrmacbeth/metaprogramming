import Lean.Elab.Command
import Lean.Meta.InferType
import Lean.ScopedEnvExtension

open Lean Meta

/-- Parse a lemma to see whether it has the correct form for a "cancellation" (`cancel`) lemma. Such
lemmas must have a conclusion of a form such `x₁ ∼ x₂`; that is, a relation between two free
variables.

The last antecedent of such a lemma must have the form `f a x₁ b c ∼' f a x₂ b c`; that is, a
relation between the application of a function to two argument lists, with one "varying argument"
pair relating the two free variables (`x₁`, `x₂`, in either order) from the conclusion, and all
other arguments (`a`, `b`, `c`) being the same on both sides. The other antecedents of such a lemma
are considered to generate "side goals".

If the given declaration is a valid `@[cancel]` lemma, we return the relation `~'` and function `f`
identified in the key hypothesis, together with the index of the "varying" argument pair in the
argument list of `f`. -/
def parseCancelLemma (decl : Name) : MetaM (Name × Name × Nat) := do
  sorry

/-- Environment extension for "cancellation" (`cancel`) lemmas. -/
initialize cancelExt : SimpleScopedEnvExtension ((Name × Name × Nat) × Name)
    (Std.HashMap (Name × Name × Nat) (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (n, lem) => m.insert n ((m.getD n #[]).push lem)
    initial := {}
  }

/-- Attribute marking "cancellation" (`cancel`) lemmas. -/
initialize registerBuiltinAttribute {
  name := `cancel
  descr := "cancellation"
  add decl _ kind := do
    -- parse the proposed cancellation lemma to find the the relation `~'` and function `f`
    -- identified in the key hypothesis, together with the index of the "varying" argument pair in
    -- the argument list of `f`.
    let key : Name × Name × Nat ← MetaM.run' (parseCancelLemma decl)
    trace[debug] "Recorded as a cancellation lemma for {key}"
    -- store this lemma in the environment extension for cancellation lemmas, with the relation,
    -- function and argument index jointly serving as the lookup key for this lemma.
    cancelExt.add (key, decl) kind
}

/-- This command lets the user check on the current state of the environment extension storing the
`@[cancel]` lemmas. -/
elab "#query_cancel_lemmas" e0:(ppSpace colGt name)? e1:(ppSpace colGt name)?
    e2:(ppSpace colGt num)? : command => do
  let (some e0, some e1, some e2) := (e0, e1, e2) |
    logInfo "Please provide the relation, function and index for the cancellation hypothesis type \
      you are interested in"
  let rel : Name := TSyntax.getName e0
  let f : Name := TSyntax.getName e1
  let i : Nat := TSyntax.getNat e2
  match (cancelExt.getState (← getEnv))[(rel, f, i)]? with
  | some lems => logInfo m!"{lems}"
  | none => logInfo "No lemmas with this key found"
