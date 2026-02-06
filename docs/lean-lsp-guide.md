# Lean LSP Guide

This guide covers the Lean Language Server Protocol (LSP) tools available via the MCP (Model Context Protocol) server for interactive development and proof exploration.

## Overview

The Lean LSP MCP server provides programmatic access to Lean 4's language server capabilities, enabling:
- Interactive proof exploration without editing files
- Type information and documentation lookup
- Code completion and symbol search
- Performance profiling of proofs
- Diagnostic checking (errors/warnings)
- Mathlib lemma search via multiple backends

All line and column numbers are **1-indexed**.

## Core Tools

### 1. `lean_goal` - Proof State Inspection

Get the proof goals at a specific position in a proof. **Most important tool - use often!**

```bash
# Omit column to see goals_before (start of line) and goals_after (end of line)
lean_goal file_path line [column]
```

**Example:**
```
File: AdderProofs.lean, Line 49
Code: cases a <;> cases b <;> cases cin <;> native_decide

goals_before:
  a b cin : Bool
  ⊢ (full adder correctness property)

goals_after: []  # Empty = proof complete!
```

**Use cases:**
- Check if a proof step closes all goals
- Understand what remains to be proven
- Debug why a tactic failed
- See how tactics transform the goal state

### 2. `lean_hover_info` - Type Signatures and Documentation

Get type signature and docs for a symbol. Column must be at the **START** of the identifier.

```bash
lean_hover_info file_path line column
```

**Example:**
```
Symbol: QueueState.empty
Type: {α : Type} (capacity : Nat) : QueueState α
Import: Shoumei.Circuits.Sequential.Queue
```

**Use cases:**
- Understand function signatures
- Check type parameters
- Find where symbols are defined
- Read inline documentation

### 3. `lean_diagnostic_messages` - Compiler Errors/Warnings

Get all diagnostics (errors, warnings, infos) for a file. Optionally filter by line range or declaration.

```bash
lean_diagnostic_messages file_path [start_line] [end_line] [declaration_name]
```

**Example outputs:**
- ✅ `{"success": true, "items": []}` - No errors
- ⚠️ `{"severity": "warning", "message": "declaration uses 'sorry'", "line": 42}`
- ❌ `{"severity": "error", "message": "Tactic rfl failed: ...", "line": 78}`

**Common messages:**
- "no goals to be solved" → Remove unnecessary tactics
- "Expected type must not contain free variables" → Can't use `native_decide` with parameters
- "declaration uses 'sorry'" → Incomplete proof

### 4. `lean_multi_attempt` - Test Tactics Without Editing

**THE MOST POWERFUL FEATURE**: Try multiple tactics at a position without modifying the file. Returns goal state and diagnostics for each.

```bash
lean_multi_attempt file_path line snippets:["tactic1", "tactic2", "tactic3"]
```

**Example:**
```json
{
  "items": [
    {"snippet": "rfl", "goals": [], "diagnostics": []},  // ✅ Works!
    {"snippet": "simp", "goals": ["..."], "diagnostics": [{"severity": "error", "message": "simp made no progress"}]},  // ❌ Fails
    {"snippet": "native_decide", "goals": [], "diagnostics": []},  // ✅ Works!
    {"snippet": "omega", "goals": ["..."], "diagnostics": [{"severity": "error", "message": "omega could not prove..."}]}  // ❌ Fails
  ]
}
```

**Recommended tactics to try:**
- `rfl` - Reflexivity (definitional equality)
- `simp` - Simplification
- `simp [lemma1, lemma2]` - Simplification with hints
- `native_decide` - Concrete evaluation (no free variables)
- `omega` - Linear arithmetic
- `ring` - Ring arithmetic
- `aesop` - Automated proof search
- `decide` - Decidable propositions
- `constructor` - Construct proofs

**Best practice:** Try 3-5 tactics at once to quickly find what works.

### 5. `lean_file_outline` - File Structure

Get imports and declarations with type signatures. **Token-efficient** way to understand file contents.

```bash
lean_file_outline file_path
```

**Returns:**
- All imports
- Declarations with name, kind (Def/Thm/structure), line numbers, type signatures
- Nested namespaces

**Use cases:**
- Quick overview of a file's contents
- Find theorem names and locations
- Understand file dependencies

### 6. `lean_completions` - IDE Autocompletion

Get IDE autocompletions at a position. Use on **INCOMPLETE** code (after `.` or partial name).

```bash
lean_completions file_path line column [max_completions:32]
```

**Example:**
```lean
QueueState.  |← cursor here gets completions for QueueState members
```

**Use cases:**
- Explore available methods on a type
- Find field names in structures
- Discover tactics and keywords

### 7. `lean_run_code` - Execute Standalone Snippets

Run a code snippet and return diagnostics. **Must include all imports.**

```bash
lean_run_code code:"import statements\n\ndefinitions\n\n#eval expressions"
```

**Example:**
```lean
-- Test basic Lean code
def greet (name : String) : String := s!"Hello, {name}!"

#eval greet "World"  -- Shows info: "Hello, World!"

theorem simple : 2 + 2 = 4 := by rfl

#check simple  -- Shows info: simple : 2 + 2 = 4
```

**Testing errors:**
```lean
theorem broken : 2 + 2 = 5 := by rfl
-- Error: Tactic rfl failed: The left-hand side 2 + 2
-- is not definitionally equal to the right-hand side 5

def typeMismatch : Nat := "string"
-- Error: Type mismatch, has type String but expected Nat
```

**Use cases:**
- Test hypotheses before editing files
- Verify lemma applications
- Prototype definitions
- Debug type errors in isolation

### 8. `lean_profile_proof` - Performance Analysis

Run `lean --profile` on a theorem. Returns per-line timing and category breakdown. **SLOW - use sparingly!**

```bash
lean_profile_proof file_path line [top_n:5] [timeout:60]
```

**Example output:**
```json
{
  "ms": 7.3,
  "lines": [
    {"line": 49, "ms": 7.2, "text": "native_decide"}
  ],
  "categories": {
    "type checking": 2.3,
    "elaboration": 1.6,
    "typeclass inference": 1.6,
    "tactic execution": 1.4,
    "compilation (LCNF base)": 1.2
  }
}
```

**Use cases:**
- Identify slow tactics
- Optimize proof performance
- Debug timeouts
- Compare tactic efficiency

## Search Tools

All search tools have **rate limits** - use judiciously!

### 9. `lean_local_search` - Fast Local Symbol Search

Search for declarations in your project. **FAST - use before trying lemma names!**

```bash
lean_local_search query [limit:10] [project_root]
```

**Example:**
```bash
lean_local_search "evalCircuit"
→ [{"name": "evalCircuit", "kind": "def", "file": "lean/Shoumei/Semantics.lean"}]

lean_local_search "Queue"
→ [{"name": "QueueState", "kind": "structure", "file": "..."}, ...]
```

**Use cases:**
- Verify declarations exist before using them
- Find where symbols are defined
- Explore project structure

### 10. `lean_leansearch` - Natural Language Search (3 req/30s)

Search Mathlib via leansearch.net using natural language or Lean terms.

```bash
lean_leansearch query [num_results:5]
```

**Example queries:**
- `"sum of two even numbers is even"`
- `"Cauchy-Schwarz inequality"`
- `"{f : A → B} (hf : Injective f) : ∃ g, LeftInverse g f"`
- `"list length empty is zero"`

**Example output:**
```json
{
  "items": [
    {
      "name": "List.length_nil",
      "module_name": "Mathlib.Data.List.Basic",
      "type": "∀ {α : Type}, List.nil.length = 0"
    }
  ]
}
```

### 11. `lean_loogle` - Type Signature Search (3 req/30s)

Search Mathlib by type signature via loogle.lean-lang.org.

```bash
lean_loogle query [num_results:8]
```

**Example queries:**
- `Real.sin` - Find theorems about sin
- `"comm"` - Find commutativity lemmas
- `(?a → ?b) → List ?a → List ?b` - Type pattern matching
- `_ * (_ ^ _)` - Wildcard patterns
- `|- _ < _ → _ + 1 < _ + 1` - Goal patterns

**Use cases:**
- Find lemmas by type signature
- Discover relevant theorems
- Type-driven search

### 12. `lean_leanfinder` - Semantic Search (10 req/30s)

Semantic search by mathematical meaning via Lean Finder.

```bash
lean_leanfinder query [num_results:5]
```

**Example queries:**
- `"commutativity of addition on natural numbers"`
- `"I have h : n < m and need n + 1 < m + 1"`
- Proof state descriptions

**Use cases:**
- Mathematical concept search
- Find lemmas matching proof context
- Natural language theorem discovery

### 13. `lean_state_search` - Goal-Based Search (3 req/30s)

Find lemmas to close the goal at a position. Searches premise-search.com.

```bash
lean_state_search file_path line column [num_results:5]
```

**Use cases:**
- Get suggestions to close current goal
- Discover relevant lemmas automatically
- Automated proof assistance

### 14. `lean_hammer_premise` - Automation Hints (3 req/30s)

Get premise suggestions for automation tactics at a goal position.

```bash
lean_hammer_premise file_path line column [num_results:32]
```

**Returns lemma names to try with:**
- `simp only [lemma1, lemma2, ...]`
- `aesop`
- As hints to other tactics

## Utility Tools

### 15. `lean_declaration_file` - Find Symbol Source

Get the file where a symbol is declared. **Symbol must be present in the file first.**

```bash
lean_declaration_file file_path symbol
```

**Example:**
```bash
lean_declaration_file "AdderProofs.lean" "QueueState"
→ "lean/Shoumei/Circuits/Sequential/Queue.lean"
```

### 16. `lean_term_goal` - Expected Type at Position

Get the expected type at a position (for incomplete terms).

```bash
lean_term_goal file_path line [column]
```

**Use cases:**
- Understand what type is expected
- Debug type errors
- Fill in `_` placeholders

### 17. `lean_build` - Rebuild Project (SLOW!)

Build the Lean project and restart LSP. **Only use if needed** (e.g., new imports).

```bash
lean_build [lean_project_path] [clean:false] [output_lines:20]
```

**When to use:**
- After adding new dependencies
- When LSP gets confused
- After modifying build files

**When NOT to use:**
- Regular development (LSP auto-rebuilds incrementally)
- After editing proof files
- Multiple times in succession

## Search Decision Tree

When looking for lemmas, follow this priority:

1. **"Does X exist locally?"** → `lean_local_search`
2. **"I need a lemma that says X"** → `lean_leansearch`
3. **"Find lemma with type pattern"** → `lean_loogle`
4. **"What's the Lean name for concept X?"** → `lean_leanfinder`
5. **"What closes this goal?"** → `lean_state_search`
6. **"What to feed simp/aesop?"** → `lean_hammer_premise`

After finding a name:
1. `lean_local_search` to verify it exists
2. `lean_hover_info` for full signature

## Common Workflows

### Debugging a Failed Proof

```bash
# 1. Check the goal state
lean_goal file_path line

# 2. Try multiple tactics
lean_multi_attempt file_path line ["rfl", "simp", "omega", "ring"]

# 3. Search for relevant lemmas
lean_leansearch "describe what you need"

# 4. Check diagnostics for hints
lean_diagnostic_messages file_path
```

### Exploring a New File

```bash
# 1. Get file structure
lean_file_outline file_path

# 2. Check hover info on key definitions
lean_hover_info file_path line column

# 3. Search for related symbols locally
lean_local_search "keyword"

# 4. Check goals in proofs
lean_goal file_path proof_line
```

### Optimizing a Slow Proof

```bash
# 1. Profile the proof
lean_profile_proof file_path theorem_line

# 2. Check which lines are slowest
# (Look at "lines" array in output)

# 3. Try alternative tactics
lean_multi_attempt file_path slow_line ["alternative1", "alternative2"]

# 4. Re-profile after changes
lean_profile_proof file_path theorem_line
```

### Testing Hypotheses

```bash
# 1. Write standalone code snippet
lean_run_code "
import Mathlib

theorem my_hypothesis : ... := by
  sorry
"

# 2. Check diagnostics
# If no errors → hypothesis is well-typed

# 3. Try tactics
# Edit snippet to test different approaches

# 4. Once working, copy to main file
```

## Error Handling

### Understanding Return Values

- **`isError: true`** → Tool failed (timeout, LSP error)
- **`isError: false, items: []`** → Success, but no results found
- **Empty goals `[]`** → Proof complete / no goals to solve
- **Diagnostics with severity "error"** → Compilation/tactic failures

### Common Error Messages

| Message | Meaning | Solution |
|---------|---------|----------|
| `"simp made no progress"` | Simp has nothing to simplify | Add lemma hints: `simp [lemma1]` |
| `"Expected type must not contain free variables"` | Can't use `native_decide` with parameters | Use case analysis first or different tactic |
| `"declaration uses 'sorry'"` | Proof is incomplete | Replace `sorry` with actual proof |
| `"no goals to be solved"` | Extra tactic after proof done | Remove the tactic |
| `"omega could not prove the goal"` | Goal is beyond omega's scope | Try different tactic or add lemmas |
| `"Tactic rfl failed"` | Not definitionally equal | Use `simp`, case analysis, or manual rewriting |

## Best Practices

1. **Use `lean_multi_attempt` generously** - It's faster than trial-and-error editing
2. **Search locally first** - `lean_local_search` before external searches
3. **Check goals often** - Understand proof state at each step
4. **Profile only when needed** - It's slow and usually unnecessary
5. **Respect rate limits** - External searches are limited (3-10 req/30s)
6. **Hover for context** - Type signatures clarify usage
7. **Test in isolation** - `lean_run_code` for experiments
8. **Don't over-build** - LSP handles incremental builds automatically

## Tips for Hardware Verification (Shoumei)

### Structural Properties

Use `native_decide` for concrete circuits:
```lean
theorem circuit_gate_count : myCircuit.gates.length = 42 := by native_decide
theorem circuit_ports : myCircuit.inputs.length = 8 := by native_decide
```

### Behavioral Properties

Use `simp` for generic proofs:
```lean
theorem read_after_write (tag : Fin n) (val : UInt32) :
    (state.write tag val).read tag = val := by
  simp [write, read]
```

Use case analysis for parameterized concrete proofs:
```lean
theorem queue_fifo (a b : Bool) :
    enqueue_then_dequeue_correct a b := by
  cases a <;> cases b <;> native_decide
```

### Checking Tool Results

After using `multi_attempt`, the tactic that closes all goals (`"goals": []`) is the one to use.

### Circuit Exploration

```bash
# 1. Find circuit definition
lean_local_search "MyCircuitName"

# 2. Get file structure
lean_file_outline path/to/circuit/file.lean

# 3. Check circuit properties
lean_hover_info path line column  # on circuit name

# 4. Explore proofs
lean_goal path proof_line  # see what's being proven
```

## Comparison with Other Tools

| Task | Lean LSP MCP | Direct Lean 4 | VSCode Extension |
|------|--------------|---------------|------------------|
| Goal inspection | ✅ Programmatic | 👁️ Visual only | 👁️ Visual only |
| Try tactics | ✅ `multi_attempt` | ❌ Must edit | ❌ Must edit |
| Run snippets | ✅ `run_code` | ✅ REPL | ⚠️ Must create file |
| Search Mathlib | ✅ All 4 backends | ❌ Manual web | ⚠️ Limited |
| Batch operations | ✅ Scriptable | ❌ Interactive | ❌ Interactive |
| Profile proofs | ✅ Built-in | ✅ CLI flag | ❌ No |

## Further Reading

- [Lean 4 Manual](https://lean-lang.org/lean4/doc/)
- [Lean 4 Theorem Proving](https://lean-lang.org/theorem_proving_in_lean4/)
- [Mathlib4 Docs](https://leanprover-community.github.io/mathlib4_docs/)
- [Lean Search Tools](https://leanprover-community.github.io/lean-search/)
- Shoumei docs: `docs/proof-strategies.md`, `docs/verification-guide.md`
