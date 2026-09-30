# Lean LSP guide

This guide covers the Lean Language Server Protocol (LSP) tools available through the MCP (Model Context Protocol) server. These tools support interactive development and proof exploration.

## Overview

The Lean LSP MCP server provides programmatic access to Lean 4's language server capabilities. It enables:
- Interactive proof exploration without editing files
- Type information and documentation lookup
- Code completion and symbol search
- Performance profiling of proofs
- Diagnostic checking (errors/warnings)
- Mathlib lemma search through multiple backends

All line and column numbers are **1-indexed**.

## Core tools

### 1. `lean_goal`: proof state inspection

Get the proof goals at a specific position in a proof. This is the most important tool, so use it often.

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
- Understand what still needs proof
- Debug why a tactic failed
- See how tactics transform the goal state

### 2. `lean_hover_info`: type signatures and documentation

Get the type signature and docs for a symbol. The column must be at the start of the identifier.

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
- Find symbol definitions
- Read inline documentation

### 3. `lean_diagnostic_messages`: compiler errors and warnings

Get all diagnostics (errors, warnings, infos) for a file. You can filter by line range or declaration.

```bash
lean_diagnostic_messages file_path [start_line] [end_line] [declaration_name]
```

**Example outputs:**
- Success: `{"success": true, "items": []}` - No errors
- Warning: `{"severity": "warning", "message": "declaration uses 'sorry'", "line": 42}`
- Error: `{"severity": "error", "message": "Tactic rfl failed: ...", "line": 78}`

**Common messages:**
- "no goals to be solved": remove unnecessary tactics.
- "Expected type must not contain free variables": you cannot use `native_decide` with parameters.
- "declaration uses 'sorry'": the proof is incomplete.

### 4. `lean_multi_attempt`: test tactics without editing

Try multiple tactics at a position without modifying the file. The tool returns the goal state and diagnostics for each.

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

**Best practice:** Try 3-5 tactics at once to find what works quickly.

### 5. `lean_file_outline`: file structure

Get imports and declarations with type signatures. This is a token-efficient way to understand file contents.

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

### 6. `lean_completions`: IDE autocompletion

Get IDE autocompletions at a position. Use it on incomplete code (after `.` or a partial name).

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

### 7. `lean_run_code`: execute standalone snippets

Run a code snippet and return diagnostics. The code must include all imports.

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

### 8. `lean_profile_proof`: performance analysis

Run `lean --profile` on a theorem. The tool returns per-line timing and a category breakdown. This command is slow, so use it sparingly.

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

## Search tools

All search tools have rate limits. Use them with care.

### 9. `lean_local_search`: fast local symbol search

Search for declarations in your project. This tool is fast, so use it before you try lemma names.

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
- Find symbol definitions
- Explore project structure

### 10. `lean_leansearch`: natural language search (3 req/30s)

Search Mathlib through leansearch.net using natural language or Lean terms.

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

### 11. `lean_loogle`: type signature search (3 req/30s)

Search Mathlib by type signature through loogle.lean-lang.org.

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

### 12. `lean_leanfinder`: semantic search (10 req/30s)

Semantic search by mathematical meaning through Lean Finder.

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

### 13. `lean_state_search`: goal-based search (3 req/30s)

Find lemmas to close the goal at a position. Searches premise-search.com.

```bash
lean_state_search file_path line column [num_results:5]
```

**Use cases:**
- Get suggestions to close current goal
- Discover relevant lemmas automatically
- Automated proof assistance

### 14. `lean_hammer_premise`: automation hints (3 req/30s)

Get premise suggestions for automation tactics at a goal position.

```bash
lean_hammer_premise file_path line column [num_results:32]
```

**Returns lemma names to try with:**
- `simp only [lemma1, lemma2, ...]`
- `aesop`
- As hints to other tactics

## Utility tools

### 15. `lean_declaration_file`: find symbol source

Find the file that declares a symbol. The symbol must be present in the file first.

```bash
lean_declaration_file file_path symbol
```

**Example:**
```bash
lean_declaration_file "AdderProofs.lean" "QueueState"
→ "lean/Shoumei/Circuits/Sequential/Queue.lean"
```

### 16. `lean_term_goal`: expected type at position

Get the expected type at a position (for incomplete terms).

```bash
lean_term_goal file_path line [column]
```

**Use cases:**
- Know which type Lean expects here
- Debug type errors
- Fill in `_` placeholders

### 17. `lean_build`: rebuild project (slow)

Build the Lean project and restart LSP. Use it only when needed, for example after new imports.

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

## Search decision tree

When looking for lemmas, follow this priority:

1. "Does X exist locally?": use `lean_local_search`.
2. "I need a lemma that says X": use `lean_leansearch`.
3. "Find a lemma with a type pattern": use `lean_loogle`.
4. "What is the Lean name for concept X?": use `lean_leanfinder`.
5. "What closes this goal?": use `lean_state_search`.
6. "What do I feed simp or aesop?": use `lean_hammer_premise`.

After finding a name:
1. `lean_local_search` to verify it exists
2. `lean_hover_info` for full signature

## Common workflows

### Debugging a failed proof

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

### Exploring a new file

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

### Optimizing a slow proof

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

### Testing hypotheses

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

## Error handling

### Understanding return values

- `isError: true`: the tool failed (timeout, LSP error).
- `isError: false, items: []`: success, but no results found.
- Empty goals `[]`: the proof is complete, with no goals to solve.
- Diagnostics with severity "error": compilation or tactic failures.

### Common error messages

| Message | Meaning | Solution |
|---------|---------|----------|
| `"simp made no progress"` | Simp has nothing to simplify | Add lemma hints: `simp [lemma1]` |
| `"Expected type must not contain free variables"` | Cannot use `native_decide` with parameters | Use case analysis first or different tactic |
| `"declaration uses 'sorry'"` | Proof is incomplete | Replace `sorry` with actual proof |
| `"no goals to be solved"` | Extra tactic after proof done | Remove the tactic |
| `"omega could not prove the goal"` | Goal is beyond omega's scope | Try different tactic or add lemmas |
| `"Tactic rfl failed"` | Not definitionally equal | Use `simp`, case analysis, or manual rewriting |

## Best practices

1. **Use `lean_multi_attempt` generously**: it is faster than trial-and-error editing.
2. **Search locally first**: run `lean_local_search` before external searches.
3. **Check goals often**: understand the proof state at each step.
4. **Profile only when needed**: it is slow and usually unnecessary.
5. **Respect rate limits**: external searches have a limit (3-10 req/30s).
6. **Hover for context**: type signatures clarify usage.
7. **Test in isolation**: use `lean_run_code` for experiments.
8. **Do not over-build**: LSP handles incremental builds automatically.

## Tips for hardware verification (Shoumei)

### Structural properties

Use `native_decide` for concrete circuits:
```lean
theorem circuit_gate_count : myCircuit.gates.length = 42 := by native_decide
theorem circuit_ports : myCircuit.inputs.length = 8 := by native_decide
```

### Behavioral properties

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

### Checking tool results

After using `multi_attempt`, the tactic that closes all goals (`"goals": []`) is the one to use.

### Circuit exploration

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

## Comparison with other tools

| Task | Lean LSP MCP | Direct Lean 4 | VSCode Extension |
|------|--------------|---------------|------------------|
| Goal inspection | Yes, programmatic | Visual only | Visual only |
| Try tactics | Yes, `multi_attempt` | No, must edit | No, must edit |
| Run snippets | Yes, `run_code` | Yes, REPL | Partial, must create file |
| Search Mathlib | Yes, all 4 backends | No, manual web | Partial, limited |
| Batch operations | Yes, scriptable | No, interactive | No, interactive |
| Profile proofs | Yes, built-in | Yes, CLI flag | No |

## Further reading

- [Lean 4 Manual](https://lean-lang.org/lean4/doc/)
- [Lean 4 Theorem Proving](https://lean-lang.org/theorem_proving_in_lean4/)
- [Mathlib4 Docs](https://leanprover-community.github.io/mathlib4_docs/)
- [Lean Search Tools](https://leanprover-community.github.io/lean-search/)
- Shoumei docs: `docs/proof-strategies.md`, `docs/verification-guide.md`
