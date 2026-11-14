# Guide to the construction notation

This folder holds a notation for writing down how to construct numbers in PowerPoint, and
`CONSTRUCTIONS.md`, the running catalogue of constructions written in it. This guide explains
how the catalogue is laid out and why.

## Purpose

The notation is for **communicating constructions** between people: a reader should be able
to follow an entry and carry it out with PowerPoint's tools. It is a recipe notation, not a
proof notation. Why a construction works, and the proof that it does, belong in the Lean
files or in the prose of a guide; they are left out of the entries on purpose.

## Structure of `CONSTRUCTIONS.md`

1. **Primitives.** A table of the operations everything else is built from. Each one is
   something you do in PowerPoint, and each matches a constructor of `Pptc/Defs.lean`.
2. **Entries**, in dependency order. Every entry uses only the primitives and the entries
   above it, so the file can be read top to bottom.
3. **Examples** sit directly under the entry they illustrate.

New entries go below everything they use. Nothing is ever used before it is defined.

## Format of an entry

```
### log₂ a

  log₂ a := Crossing( ExpGraph, Line((−N, a), (N, a)) ).x            a > 0

  N : a whole number larger than |log₂ a|
```

- The heading is the name being defined, written exactly as it will be used.
- `:=` gives the definition. Once defined, the name can be used anywhere below.
- Conditions on the inputs (`a > 0`) are written at the right of the definition line.
- `with` introduces helper quantities used only in that definition.
- `N : …` lines are **choices**: a number the reader picks, usually from an approximation,
  such as the length of a line or an interval around a root. Any choice meeting the
  description works.

## Conventions

**Use mathematical notation wherever it exists.** If a construction produces something with a
standard name or symbol, the entry defines that symbol: `aᵇ`, `log₂ a`, `√a`, `π`, not
`Power(a, b)` or `Log2(a)`. Readers already know these, and they keep later entries short.

**Use function names for drawing operations.** Geometric steps have no standard symbol, so
they get descriptive names with capitals: `Line(P, Q)`, `Crossing(C, D)`, `Crop(C, …)`.
Curves are named the same way: `ExpGraph`, `UnitCircle`, `Parabola`.

**Read coordinates with `.x` and `.y`.** `Crossing(C, D)` is a point; `Crossing(C, D).x` is its
x-coordinate.

**One crossing at a time.** `Crossing(C, D)` requires that C and D meet in exactly one point.
When two curves would cross more than once, the entry draws or crops them so that only the
wanted crossing is left. This is what you would do in PowerPoint anyway, and it means the
notation needs no separate way of choosing between crossings.

**Lines have ends.** A drawn line is a segment, so an entry that needs a line says how long it
is, usually through a choice `N : a whole number larger than …`.

**Words only where they help.** Short words like `with`, `if` and the descriptions in choice
lines are fine. Explanations of *why* are not part of an entry.

## Primitives and PowerPoint

Every primitive should be an action a reader can perform. Where the exact PowerPoint steps are
long or still being worked out (cropping and measuring length), the primitive is taken as
given and its table row says so. Adding a primitive is a bigger step than adding an entry: it
should match a constructor in `Pptc/Defs.lean`.
