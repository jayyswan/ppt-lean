# Constructions

The notation is explained in `GUIDE.md`. Entries are in dependency order.

## Contents

- [Primitives](#primitives)
- [π](#π)
- [√a](#a)
- [log₂ a](#log₂-a)
- [2ᶜ](#2ᶜ)
- [aᵇ](#aᵇ)

---

## Primitives

| primitive | what it does | in PowerPoint | in `Defs.lean` |
|---|---|---|---|
| `+ − × ÷` | arithmetic on constructed numbers | taken as given | `add`, `sub`, `mul`, `div` |
| `Line(P, Q)` | line segment from P to Q | Line tool | an edge of a `rectangle`, cropped |
| `Circle(C, r)` | circle with centre C and radius r | Oval, width = height = 2r | `ellipse` |
| `PolynomialGraph(p)` | the curve y = p(x); p of degree ≤ 6, rational coefficients | chart with a polynomial trendline | `poly_graph` |
| `ExpGraph` | the curve y = 2ˣ | chart with an exponential trendline through (0, 1), (1, 2) | `exp_two` |
| `Crop(C, xmin, xmax, ymin, ymax)` | the part of C inside that rectangle | taken as given | `restrict` |
| `Length(C)` | the length of the curve C | taken as given | `arc_length` |
| `Crossing(C, D)` | the single point where C and D cross | read the crossing point | `inter_x`, `inter_y` |

---

## π

```
UnitCircle := Circle((0, 0), 1)

π := Length( Crop(UnitCircle, xmin = −1, xmax = 1, ymin = 0, ymax = 1) )
```

---

## √a

```
√a := Crossing( PolynomialGraph(x²), Line((0, a), (N, a)) ).x          a > 0

  N : a whole number larger than √a
```

Example: √2

```
√2 = Crossing( PolynomialGraph(x²), Line((0, 2), (2, 2)) ).x           ≈ 1.414
```

---

## log₂ a

```
log₂ a := Crossing( ExpGraph, Line((−N, a), (N, a)) ).x                a > 0

  N : a whole number larger than |log₂ a|
```

---

## 2ᶜ

```
2ᶜ := Crossing( ExpGraph, Line((c, 0), (c, N)) ).y

  N : a whole number larger than 2ᶜ
```

---

## aᵇ

```
aᵇ := 2^(b · log₂ a)                                                   a > 0
```

Example: 3^(1/2)

```
log₂ 3   = Crossing( ExpGraph, Line((−2, 3), (2, 3)) ).x                         ≈ 1.585
3^(1/2)  = 2^(½ log₂ 3) = Crossing( ExpGraph, Line((½ log₂ 3, 0), (½ log₂ 3, 2)) ).y   ≈ 1.732
```
