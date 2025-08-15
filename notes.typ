
#import "@preview/ctheorems:1.1.3": *
#import "@preview/fletcher:0.5.7" as fletcher: diagram, edge, node
#set text(font: "New Computer Modern")
#set document(title: [Notes on Fibrations], author: "Adrien Mathieu")
#set heading(numbering: "1.")
#show: thmrules.with(qed-symbol: $square$)

#let definition = thmbox("definition", "Definition", inset: (top: .5em))
#let theorem = thmbox("theorem", "Theorem", inset: (top: .5em))
#let lemma = thmbox("lemma", "Lemma", inset: (top: .5em))
#let proof = thmproof("proof", "Proof")
#let Cat = [*Cat*]
#let Fib(C) = $#[*Fib*] _(#C)$
#let Pfct(C) = $#[*Pfct*] _(#C)$
#v(20%)
#align(center, text(25pt)[*Notes on Grothendieck Fibrations*])
#align(center, text(15pt)[Adrien #smallcaps([Mathieu])])
#v(10%)
#outline()
#pagebreak()

#set page(
  footer: align(
    center,
    context counter(page).display("-- 1 --"),
  ),
)
#counter(page).update(1)

= Introduction

== Preliminary definitions

In this section, we have two categories $cal(B)$ and $cal(E)$, and a functor $p : cal(E) arrow
cal(B)$.
#definition("Refinement")[
  Let $R : cal(E)$ and $X : cal(B)$.  We say that _$R$ refines $X$_, or $R subset.sq X$, if $ X = p(R) $
]

We note #diagram($R edge("-[]") & X$) to mean $R subset.sq X$, and we say that the following diagram commutes
#align(center)[#diagram(
  spacing: 2cm,
  $
    S edge("d", "-[]") edge(alpha, ->) & R edge("d", "-[]") \
                         X edge(f, ->) & Y
  $,
)]
if $f = p(alpha)$.

#definition("Cartesian morphism")[
  Let $R, S : cal(E)$.  A morphism $alpha : S arrow R$ is _cartesian_ if, for any
  $S' : cal(E)$, $alpha' : S' arrow R$, and $f : p(S') arrow p(S)$ such that the following diagram
  commutes
  #align(center)[#diagram(
    spacing: 2cm,
    $
      p(S') edge(p(alpha'), ->) edge("d", f, ->) & p(R) \
                   p(S) edge("ur", p(alpha), ->)
    $,
  )]
  There exists a unique $hat(f) : S' arrow S$ such that $f = p(hat(f))$, and such that the following
  diagram commutes
  #align(center)[#diagram(
    spacing: 2cm,
    $
      S' edge(alpha', ->) edge("d", hat(f), ->, "dashed") & R \
                                  S edge("ur", alpha, ->)
    $,
  )]
]

#lemma()[
  A cartesian morphism is an isomorphism.
]<cartesian-iso>
#proof()[
  Let $R,S : cal(E)$ and $alpha : R arrow S$ be a cartesian morphism in $cal(E)$.
]

#definition("Fibration")[
  $p$ is said to be a _fibration_ if, for any
  #align(center)[#diagram(
    spacing: 2cm,
    $
                    & R edge("d", "-[]") \
      X edge(f, ->) & Y
    $,
  )]
  there exists a cartesion morphism $alpha$ making the following commute
  #align(center)[#diagram(
    spacing: 2cm,
    $
      S edge(alpha, ->) edge("d", "-[]") & R edge("d", "-[]") \
                           X edge(f, ->) & Y
    $,
  )]
]

#definition([Category of fibrations])[
  For a base category $cal(B)$, define $Fib(cal(B))$ as the category of fibrations over
  $cal(B)$, that is, whose objects are pairs $(cal(E), p)$ with $cal(E)$ a category and
  $p : cal(E) arrow cal(B)$ a fibration.

  Given two fibrations $p_i : cal(E)_i arrow cal(B)$ over $cal(B)$ for $i=1,2$, a morphism of
  fibrations between $p_1$ and $p_2$ is a functor $F : cal(E)_1 arrow cal(E)_2$ making the
  following diagram commute
  #align(center)[#diagram(
    spacing: 2cm,
    $
      cal(E)_1 edge(F, ->) edge("d", p_1, ->) & cal(E)_2 edge("d", p_2, ->) \
                 cal(B) edge(id_(cal(B)), ->) & cal(B)
    $,
  )]
  and which preserves cartesianity of morphisms.
]

#definition([Category of pseudofunctors])[
  For a given base category $cal(B)$, define $Pfct(cal(B))$ as the category whose elements
  are contravariant pseudo-functors $cal(P) : cal(B)^(op) arrow Cat$ in $Cat$, that is,
  - #box(width: 100%)[for each object $X : cal(B)$, a category $cal(P)_X$;]
  - for each morphism $f : X arrow Y$ in $cal(B)$, a functor $cal(P)_f : cal(P)_Y arrow cal(P)_X$;
  - for each object $X : cal(B)$, a natural isomorphism $ i_X : cal(P)_(id_X) arrow.double.long id_(cal(P)_X) $
    called the pseudo unit of $cal(P)$ at $X$;
  - for each morphisms $f : X arrow Y$ and $g : Y arrow Z$ in $cal(B)$, a natural isomorphism $ c_(f, g) : cal(P)_(g compose f) arrow.double.long cal(P)_f compose cal(P)_g $
    called the pseudo composition law of $cal(P)$ at $f$ and $g$.

  We additionally require the following coherence conditions: for $f : X arrow Y$, the following
  diagram commutes
  #align(center, diagram(
    spacing: 2cm,
    $
      cal(P)_f edge(c_(f, id_Y), ->) edge("d", c_(id_X, f), ->) edge("dr", id_cal(P)_f, ->)
      & cal(P)_f compose cal(P)_(id_Y) edge("d", cal(P)_f compose i_Y, ->, label-side: #left) \
      cal(P)_(id_X) compose cal(P)_f edge(i_X compose cal(P)_f, ->, label-side: #right) & cal(P)_f
    $,
  ))
  Furthermore, for $f : W arrow X$, $g : X arrow Y$ and $h : Y arrow Z$, the following diagram
  commutes
  #align(center, diagram(
    spacing: 2cm,
    $
      cal(P)_(h compose g compose f) edge(c_(f, h compose g), ->) edge("d", c_(g compose f, h), ->)
      & cal(P)_f compose cal(P)_(h compose g) edge("d", cal(P)_f compose c_(g, h), ->) \
      cal(P)_(g compose f) compose cal(P)_h edge(c_(f, g) compose cal(P)_h, ->)
      & cal(P)_f compose cal(P)_g compose cal(P)_h
    $,
  ))

  Given two pseudofunctors $cal(P)$ and $cal(P)'$, a morphism $nu : cal(P) arrow cal(P)'$ is a
  pseudonatural transformation between $cal(P)$ and $cal(P)'$, that is, for each point $X :
  cal(B)$, a functor $nu_X : cal(P)_X arrow cal(P)'_X$ and, for each morphism $f : X arrow Y$
  in $cal(B)$, a natural isomorphism
  #align(center)[#diagram(
    spacing: 2cm,
    $
      cal(P)_Y edge(nu_Y, ->) edge("d", cal(P)_f, ->) & cal(P)'_Y edge("d", cal(P)'_f, ->) edge("dl", nu_f, =>) \
                              cal(P)_X edge(nu_X, ->) & cal(P)'_X
    $,
  )]
  satisfying the following coherence conditions:
]

- for $X : cal(B)$, the following pasting is $nu_X$
  #align(center, diagram(
    spacing: 2cm,
    $
      cal(P)_X edge("d", cal(P)_(id_X), ->) edge(nu_X, ->)
      edge("d", id_(cal(P)_X), ->, bend: #(-90deg)) & cal(P)'_X edge("d", cal(P)'_(id_X), ->) edge("dl", nu_(id_X), =>)
                                                      edge("d", id_(cal(P)'_X), ->, bend: #90deg) \
                            cal(P)_X edge(nu_X, ->) & cal(P)'_X
    $,
    edge((-.4, .5), (-.7, .5), $i_X$, "=>"),
    edge((1.7, .5), (1.04, .5), $i^(-1)_X$, "=>"),
  ))
  that is, $ (nu_X compose i_X) compose nu_(id_X) compose (i'^(-1)_X compose nu_X) = id_(nu_X) $
- if $f : X arrow Y$ and $g : Y arrow Z$ are two morphisms in $cal(B)$, $nu_(g compose f)$ is
  obtained by pasting the squares (plus pseudo-composition)
  #align(center, diagram(
    spacing: 2cm,
    $
      cal(P)_Z edge(nu_Z, ->) edge("d", cal(P)_g, ->) edge("dd", cal(P)_(g compose f), ->, bend: #(-50deg))
      & cal(P)'_Z edge("d", cal(P)'_g, ->) edge("dl", nu_g, =>)
      edge("dd", cal(P)'_(g compose f), ->, bend: #50deg)\
      cal(P)_Y edge(nu_Y, ->) edge("d", cal(P)_f, ->)
      & cal(P)'_Y edge("d", cal(P)'_f, ->) edge("dl", nu_f, =>) \
      cal(P)_X edge(nu_X, ->) & cal(P)'_X
    $,
    edge((1.5, 1), (1, 1), $c'_(f, g)$, "=>"),
    edge((0, 1), (-.5, 1), $c^(-1)_(f, g)$, "=>"),
  ))
  that is, $ nu_(g compose f) = (nu_X compose c^(-1)_(f, g)) compose (nu_f compose cal(P)_g)
  compose (cal(P)'_f compose nu_g) compose (c'_(f,g) compose nu_Z) $


== Main theorem
We aim at proving the
#theorem([Main theorem])[
  For a given base category $cal(B)$, we have $ Fib(cal(B)) tilde.equiv Pfct(cal(B)) $
]

In order to do so, we will build in @fiber-functor half of the equivalence, namely, $ Phi :
Fib(cal(B)) arrow Pfct(cal(B)) $ and, in @grothendieck-construction, the other half of the
equivalence, namely, $ Psi : Pfct(cal(B)) arrow Fib(cal(B)) $

In @equivalence, we will show that the two form the two halves of an equivalence, finishing the
proof.

= Fiber functor <fiber-functor>

Let's build $ Phi : Fib(cal(B)) arrow Pfct(cal(B)) $

== Action of $Phi$ on objects

Assume we have a fibration $p$.

=== Definition of the fibre pseudo-functor
Let us build $p^(-1) : cal(B)^(op) arrow Cat$ a pseudo-functor.
For $X : cal(B)$, $        p^(-1)_X & = { R : cal(E) | R subset.sq X } \
p^(-1)_X (S, R) & = { alpha : S arrow R | p(alpha) = id_X } $

Let $X, Y : cal(B)$ and $f : X arrow Y$. Let's define $p^(-1)_f : p^(-1)_Y arrow p^(-1)_X$ by
noticing that, for each $R : p^(-1)_Y$, by the fibration condition on $p$, there exists a
cartesian morphism $[f]_R$
#align(center)[#diagram(
  spacing: 2cm,
  $
    p^(-1)_f (R) edge("d", "-[]") edge([f]_R, ->) & R edge("d", "-[]") \
                                    X edge(f, ->) & Y
  $,
)]

Furthermore, for $R, R' : p^(-1)_Y$ and $g : R arrow R'$, we have the following diagram

#align(center)[#diagram(
  spacing: 2cm,
  $
    p^(-1)_f (R') edge("dd", "-[]", bend: #(-30deg)) edge("r", [f]_R', ->) & R' edge("dd", "-[]", bend: #30deg) \
                             p^(-1)_f (R) edge("d", "-[]") edge([f]_R, ->) & R edge("d", "-[]") edge("u", g, ->) \
                                                             X edge(f, ->) & Y
  $,
)]

By cartesianity of $iota_R'$, there exists a unique $p^(-1)_f (g) : p^(-1)_f (R) arrow p^(-1)_f (R')$ st $             p(p^(-1)_f (g)) & = id_X \
[f]_R' compose p^(-1)_f (g) & = g compose [f]_R $
ie. the following diagram commutes
#align(center)[#diagram(
  spacing: 2cm,
  $
    p^(-1)_f (R') edge("dd", "-[]", bend: #(-30deg)) edge("r", [f]_R', ->) & R' edge("dd", "-[]", bend: #30deg) \
    p^(-1)_f (R) edge("u", p^(-1)_f (g), ->, "dashed") edge("d", "-[]") edge([f]_R, ->) & R edge("d", "-[]") edge("u", g, ->)\
    X edge(f, ->) & Y
  $,
)]

Let us indeed check that this defines a functor.  For any $R : p^(-1)_Y$, note that

#align(center)[#diagram(
  spacing: 2cm,
  $
    p^(-1)_f (R) edge("dd", "-[]", bend: #(-40deg)) edge("r", [f]_R, ->) & R edge("dd", "-[]", bend: #40deg) \
    p^(-1)_f (R) edge("u", id_(p^(-1)_f (R)), ->, "dashed") edge("d", "-[]") edge([f]_R, ->) & R edge("d", "-[]") edge("u", id_R, ->)\
    X edge(f, ->) & Y
  $,
)]

$id_(p^(-1)_f (R))$ satisfies the universal property of $p^(-1)_f (id_R)$, so we have $ p^(-1)_f (id_R) = id_(p^(-1)_f (R)) $

Let now $R, R', R'' : p^(-1)_Y$, $g : R arrow R'$ and $g' : R' arrow R''$.
#align(center)[#diagram(
  spacing: 2cm,
  $
    p^(-1)_f (R'') edge("ddd", "-[]", bend: #(-35deg)) edge("r", [f]_R'', ->) & R'' edge("ddd", "-[]", bend: #35deg) \
    p^(-1)_f (R') edge("u", p^(-1)_f (g'), ->, "dashed") edge("r", [f]_R', ->) edge("dd", "-[]", bend: #(-30deg)) & R' edge("dd", "-[]", bend: #30deg) edge("u", g', ->) \
    p^(-1)_f (R) edge("u", p^(-1)_f (g), ->, "dashed") edge("d", "-[]") edge([f]_R, ->) & R edge("d", "-[]") edge("u", g, ->)\
    X edge(f, ->) & Y
  $,
)]

Note that $p^(-1)_f (g') compose p^(-1)_f (g)$ satisfies the universal property of $p^(-1)_f (g'
  compose g)$, so we have $ p^(-1)_f (g' compose g) = p^(-1)_f (g') compose p^(-1)_f (g) $

Let us now show that $p^(-1)$ indeed defines a pseudo-functor.

=== Pseudo identity law
For $X : cal(B)^(op)$, let us first exhibit a natural isomorphism $p^(-1)_(id_X)
tilde(arrow.double) id_X$.  For $R : p^(-1)_X$, we have $[id_X]_R : p^(-1)_(id_X) (R) arrow id_X
(R)$.  This defines a natural transformation.  Indeed, for $R, R' : p^(-1)_X$ and $f : R arrow
R'$, the following diagram commutes by definition of $p^(-1)_(id_X) (f)$:
#align(center)[#diagram(
  spacing: 2cm,
  $
    p^(-1)_(id_X) (R') edge("dd", "-[]", bend: #(-30deg)) edge("r", [id_X]_R', ->) & R' edge("dd", "-[]", bend: #30deg) \
    p^(-1)_(id_X) (R) edge("u", p^(-1)_(id_X) (f), ->) edge("d", "-[]") edge([id_X]_R, ->) & R edge("d", "-[]") edge("u", f, ->) \
    X edge(id_X, ->) & X
  $,
)]
So in particular the upper square commutes
#align(center)[#diagram(
  spacing: 2cm,
  $
    p^(-1)_(id_X) (R) edge([id_X]_R, ->) edge("d", p^(-1)_(id_X) (f), ->) & R edge("d", f, ->) \
                                   p^(-1)_(id_X) (R') edge([id_X]_R', ->) & R'
  $,
)]

hence $[id_X]$ is natural.  Let's show that each component is an isomorphism.

There is a unique morphism $phi : R arrow p^(-1)_(id_X) (R)$ making the following diagram commute

#align(center)[#diagram(
  spacing: 2cm,
  $
    R edge("drr", id_R, ->, bend: #20deg) edge("ddr", "-[]", bend: #(-20deg)) edge("dr", phi, ->, "dashed") \
    & p^(-1)_(id_X) (R) edge([id_X]_R, ->) edge("d", "-[]") & R edge("d", "-[]") \
    & X edge(id_X, ->) & X
  $,
)]

So $ [id_X]_R compose phi = id_R $

Furthermore, the following diagram commutes

#align(center)[#diagram(
  spacing: 2cm,
  $
    p^(-1)_(id_X) (R) edge("rrrdd", [id_X]_R, ->, bend: #30deg) edge("dddrr", "-[]", bend: #(-30deg)) edge("dr", [id_X]_R, ->) \
    & R edge("dr", phi, ->) edge("drr", id_R, ->, bend: #15deg) \
    & & p^(-1)_(id_X) (R) edge("r", [id_X]_R, ->) edge("d", "-[]") & R edge("d", "-[]") \
    & & X edge(id_X, ->) & X
  $,
)]

Meaning that $phi compose [id_X]_R$ satisfies the universal property of $[id_X]_R$ with respect to
$[id_X]_R$.  But so does the identity, so, by unicity, we have $ phi compose [id_X]_R = id_(p^(-1)_(id_X) (R)) $
Hence $[id_X]_R$ is an iso.

=== Pseudo-composition law
#lemma([Pseudo-composition law])[
  Let $X, Y, Z : cal(B)$, and $f : X arrow Y$, $g : Y arrow Z$.  There is a natural isomorphism
  $ [f, g] : p^(-1)_(g compose f) arrow.double.long p^(-1)_f compose p^(-1)_g $
]
#proof[
  Let $R : p^(-1)_Z$, and consider the following diagram
  #align(center)[#diagram(
    spacing: 2cm,
    $
      p^(-1)_(g compose f) (R) edge("ddr", "-[]") edge("rrrd", [g compose f]_R, ->, bend: #20deg) \
      & p^(-1)_f (p^(-1)_g (R)) edge("d", "-[]") edge([f]_(p^(-1)_g (R)), ->) & p^(-1)_g (R) edge([g]_R, ->) edge("d", "-[]") & R edge("d", "-[]") \
      & X edge(f, ->) & Y edge(g, ->) & Z
    $,
  )]
  The fact that $[g compose f]_R$ is cartesian gives a unique morphism $h : p^(-1)_f (p^(-1)_g (R))
  arrow p^(-1)_(g compose f) (R)$ making the diagram commute:
  #align(center)[#diagram(
    spacing: 2cm,
    $
      p^(-1)_(g compose f) (R) edge("ddr", "-[]") edge("rrrd", [g compose f]_R, ->, bend: #20deg) \
      & p^(-1)_f (p^(-1)_g (R)) edge("ul", h, ->, "dashed") edge("d", "-[]") edge([f]_(p^(-1)_g (R)), ->) & p^(-1)_g (R) edge([g]_R, ->) edge("d", "-[]") & R edge("d", "-[]") \
      & X edge(f, ->) & Y edge(g, ->) & Z
    $,
  )]

  Conversely, the cartesianity of $[g]_R$, and then $[f]_(p^(-1)_g (R))$ gives $h' : p^(-1)_(g
  compose f) (R) arrow p^(-1)_g (R)$, then $[f, g]_R : p^(-1)_(g compose f) (R) arrow p^(-1)_f (p^(-1)_g
    (R))$ making the following commute
  #align(center)[#diagram(
    spacing: 2cm,
    $
      p^(-1)_(g compose f) (R) edge("dr", [f,g]_R, ->, "dashed") edge("drr", h', ->, "dashed", bend: #8deg) edge("ddr", "-[]") edge("rrrd", [g compose f]_R, ->, bend: #20deg) \
      & p^(-1)_f (p^(-1)_g (R)) edge("d", "-[]") edge([f]_(p^(-1)_g (R)), ->) & p^(-1)_g (R) edge([g]_R, ->) edge("d", "-[]") & R edge("d", "-[]") \
      & X edge(f, ->) & Y edge(g, ->) & Z
    $,
  )]
  In particular, $[f,g]_R$ and $h$ must be each other's inverse.  We have to show that this
  construction is natural.  Let $R, R' : p^(-1)_Z$ and $h : R arrow R'$.  We want to show that the
  following diagram commutes

  #align(center)[#diagram(
    spacing: 2cm,
    $
      p^(-1)_(g compose f) (R) edge([f, g]_R, ->) edge("d", p^(-1)_(g compose f) (h), ->)
      & p^(-1)_f (p^(-1)_g (R)) edge("d", p^(-1)_f (p^(-1)_g (h)), ->) \
      p^(-1)_(g compose f) (R') edge([f, g]_R', ->) & p^(-1)_f (p^(-1)_g (R'))
    $,
  )]

  Note that in the following diagram
  #align(center)[#diagram(
    spacing: .7cm,
    $
      & p^(-1)_(g compose f) (R') edge("ddddrr", "-[]") edge("ddrr", [f, g]_R', ->) edge("ddrrrrrr", [g compose f]_R', ->, bend: #10deg) \
      p^(-1)_(g compose f) (R') edge("ur", p^(-1)_(g compose f) (h), ->) edge("ddddrr", "-[]") edge("ddrr", [f, g]_R, ->) \
      & & & p^(-1)_f (p^(-1)_g (R')) edge("dd", "-[]") edge("rr", [f]_(p^(-1)_g (R')), ->)
      & & p^(-1)_g (R') edge("dd", "-[]") edge("rr", [g]_R', ->) & & R' edge("dd", "-[]") \
      & & p^(-1)_f (p^(-1)_g (R)) edge("dd", "-[]") edge("rr", [f]_(p^(-1)_g (R)), ->, crossing: #true, label-pos: #70%) edge("ur", p^(-1)_f (p^(-1)_g (h)), ->, crossing: #true)
      & & p^(-1)_g (R) edge("rr", [g]_R, ->, crossing: #true) edge("ur", p^(-1)_g (h), ->, label-pos: #20%) & & R edge("ur", h, ->) edge("uullllll", [g compose f]_R, <-, bend: #(-10deg), crossing: #true) \
      & & & X edge("rr", f, ->) & & Y edge("rr", g, ->)& & Z \
      & & X edge("ur", id_X, ->) edge("rr", f, ->) & & Y edge("uu", "[]-", crossing: #true) edge("rr", g, ->) edge("ur", id_Y, ->) & & Z edge("ur", id_Z, ->, label-side: #right) edge("uu", "[]-", crossing: #true)
    $,
  )]

  $p^(-1)_(g compose f) (h)$ is the unique solution to the universal problem of living in the fiber
  above $X$ and making the top-most square commute.  Hence, to prove that $ [f,g]_R' compose p^(-1)_(g compose f) (h) = p^(-1)_f (p^(-1)_g (h)) compose [f, g]_R $

  it suffices to show that $[f,g]_R'^(-1) compose p^(-1)_f (p^(-1)_g (h)) compose [f, g]_R$ also satisfies
  this universal property.  Each of these three morphisms lives in the fiber above $X$, so so does their
  composition.  Furthermore, $ [g compose f]_R' compose [f,g]_R'^(-1) compose p^(-1)_f (p^(-1)_g (h)) compose [f, g]_R
  &= [g]_R' compose [f]_(p^(-1)_g (R')) compose p^(-1)_f (p^(-1)_g (h)) compose [f, g]_R
  & "by definition of" [f,g]_R' \
  &= [g]_R' compose p^(-1)_g (h) compose [f]_(p^(-1)_g (R)) compose [f, g]_R
  & "by definition of" p^(-1)_f (p^(-1)_g (h)) \
  &= h compose [g]_R compose [f]_(p^(-1)_g (R)) compose [f, g]_R
  & "by definition of" p^(-1)_g (h) \
  &= h compose [g compose f]_R
  & "by definition of" [f,g]_R $
]

=== Identity/composition coherence
Let $X,Y : cal(B)$ and $f : X arrow Y$ We have to check that the following diagram commutes
#align(center, diagram(
  spacing: 2cm,
  $
    p^(-1)_f edge([f, id_Y], ->) edge("d", [id_X, f], ->) edge("dr", id_(p^(-1)_f), ->)
    & p^(-1)_f compose p^(-1)_(id_Y) edge("d", p^(-1)_f compose [id_Y], ->, label-side: #left) \
    p^(-1)_(id_X) compose p^(-1)_f edge([id_X] compose p^(-1)_f, ->, label-side: #right) & p^(-1)_f
  $,
))

Let's show that each triangle commutes independently.

==== Upper triangle

Let $R : p^(-1)_Y$.  We have to check the commutation of the following diagram

#align(center, diagram(
  spacing: 2cm,
  $
    p^(-1)_f (R) edge([f, id_Y]_R, ->) edge("dr", id_(p^(-1)_f (R)), ->, label-side: #right)
    & p^(-1)_f (p^(-1)_id_Y (R)) edge("d", p^(-1)_f ([id_Y]_R), ->, label-side: #left) \
    & p^(-1)_f (R)
  $,
))

By definition of $[f, id_Y]$, the following diagram commutes
#align(center, diagram(
  spacing: 2cm,
  $
    p^(-1)_f (R) edge("ddr", "-[]") edge("drrr", [f]_R, ->, bend: #20deg) edge("dr", [f, id_Y]_R, ->) \
    & p^(-1)_f (p^(-1)_(id_Y) (R)) edge([f]_(p^(-1)_(id_Y) (R)), ->) edge("d", "-[]")
    & p^(-1)_(id_Y) (R) edge([id_Y]_R, ->) edge("d", "-[]") & R edge("d", "-[]") \
    & X edge(f, ->) & Y edge(id_Y, ->) & Y
  $,
))

and we also have
#align(center, diagram(
  spacing: 2cm,
  $
    p^(-1)_f (R) edge([f]_R, ->) edge("dd", "-[]", bend: #(-60deg)) & R edge("dd", "-[]", bend: #60deg) \
     p^(-1)_f (p^(-1)_(id_Y)(R)) edge("u", p^(-1)_f ([id_Y]_R), ->)
     edge([f]_(p^(-1)_(id_Y)(R)), ->) edge("d", "-[]")              & R edge("u", [id_Y]_R, ->) edge("d", "-[]") \
                                                      X edge(f, ->) & Y
  $,
))

Hence, by stitching the two together, we have that the following diagram commutes
#align(center, diagram(
  spacing: 2cm,
  $
    p^(-1)_f (R) edge("ddrrr", [f]_R, ->, bend: #20deg) edge("dr", [f, id_Y]_R, ->)
    edge("dddrr", "-[]", bend: #(-10deg)) \
    & p^(-1)_f (p^(-1)_(id_Y)(R)) edge("dr", p^(-1)_f ([id_Y]_R), ->) \
    && p^(-1)_f (R) edge([f]_R, ->) edge("d", "-[]") & R edge("d", "-[]") \
    && X edge(f, ->) & Y
  $,
))

By cartesianity of $[f]_R$, $p^(-1)_f ([id_Y]_R) compose [f, id_Y]_R$ is unique making this diagram
commute; but since so does $id_(p^(-1)_f (R))$, we must have $ p^(-1)_f ([id_Y]_R) compose [f, id_Y]_R = id_(p^(-1)_f (R)) $

==== Lower triangle

Let $R : p^(-1)_Y$. We have to show the commutation of the following diagram

#align(center, diagram(
  spacing: 2cm,
  $
           p^(-1)_f (R) edge("dr", id_(p^(-1)_f (R)), ->) edge("d", [id_X, f]_R, ->) \
    p^(-1)_(id_X) (p^(-1)_f (R)) edge([id_X]_(p^(-1)_f (R)), ->, label-side: #right) & p^(-1)_f (R)
  $,
))

By definition of $[id_X, f]$, the following diagram commutes

#align(center, diagram(
  spacing: 2cm,
  $
    p^(-1)_f (R) edge("drrr", [f]_R, ->, bend: #30deg) edge("dr", [id_X, f]_R, ->) edge("ddr", "-[]") \
    & p^(-1)_(id_X) (p^(-1)_f (R)) edge([id_X]_(p^(-1)_f (R)), ->) edge("d", "-[]")
    & p^(-1)_f (R) edge([f]_R, ->) edge("d", "-[]")
    & R edge("d", "-[]") \
    & X edge(id_X, ->) & X edge(f, ->) & Y
  $,
))

but, by cartesianity of $[f]_R$, $[id_X]_(p^(-1)_f (R)) compose [id_X, f]_R$ is unique making this
diagram commute.  Because $id_(p^(-1)_f (R))$ also makes it commute, we must have $ [id_X]_(p^(-1)_f (R)) compose [id_X, f]_R = id_(p^(-1)_f (R)) $

=== Composition/composition coherence

Let $W,X,Y,Z : cal(B)$ and
#align(center, diagram(
  spacing: 2cm,
  $
    W edge(f, ->) & X edge(g, ->) & Y edge(h, ->) & Z
  $,
))
Let $R : p^(-1)_Z$, we want to show that the following diagram commutes
#align(center, diagram(
  spacing: 2cm,
  $
    p^(-1)_(h compose g compose f) (R) edge([f, h compose g]_R, ->) edge("d", [g compose f, h]_R, ->)
    & p^(-1)_f (p^(-1)_(h compose g) (R)) edge("d", p^(-1)_f ([g, h]_R), ->) \
    p^(-1)_(g compose f) (p^(-1)_h (R)) edge([f, g]_(p^(-1)_h (R)), ->)
    & p^(-1)_f (p^(-1)_g (p^(-1)_h (R)))
  $,
))

It suffices to show that $[f,g]^(-1)_(p^(-1)_h (R)) compose p^(-1)_f ([g,h]_R) compose [f, h compose g]_R$
satisfies the universaly property of $[g compose f, h]_R$, that is, the following diagram commutes
#align(center, diagram(
  spacing: 2cm,
  $
    p^(-1)_(h compose g compose f) (R) edge([h compose g compose f]_R, ->) edge("d", [f, h compose g]_R, ->)
    & R \
    p^(-1)_f (p^(-1)_(h compose g) (R)) edge("d", p^(-1)_f ([g, h]_R), ->)
    & p^(-1)_h (R) edge("u", [h]_R, ->) \
    p^(-1)_f (p^(-1)_g (p^(-1)_h (R))) edge([f, g]^(-1)_(p^(-1)_h (R)), ->)
    & p^(-1)_(g compose f) (p^(-1)_h (R)) edge("u", [g compose f]_(p^(-1)_h (R)), ->)
  $,
))

In the following diagram, each inner diagram commutes, hence the outermost diagram commutes
#[
  #set text(size: 8pt)
  #align(center, diagram(
    spacing: 1.5cm,
    crossing-thickness: 7,
    $
      p^(-1)_(h compose g compose f) (R)
      edge("drrrrrr", [h compose g compose f]_R, ->, bend: #10deg)
      edge("dr", [f, h compose g]_R, ->)
      edge("dd", "-[]") \
      & p^(-1)_f (p^(-1)_(h compose g) (R)) edge([f]_(p^(-1)_(h compose g) (R)), ->) edge("dd", "-[]")
      edge("dr", p^(-1)_f ([g, h]_R), ->)
      & p^(-1)_(h compose g) (R) edge("rrrr", [h compose g]_R, ->) edge("dd", "-[]")
      edge("dr", [g, h]_R, ->)
      & & & & R edge("dd", "-[]") \
      W edge("dr", id_W, ->) &
      & p^(-1)_f (p^(-1)_g (p^(-1)_h (R))) edge([f]_(p^(-1)_g (p^(-1)_h (R))), ->)
      & p^(-1)_g (p^(-1)_h (R)) edge("dd", "-[]") edge("rr", [g]_(p^(-1)_h (R)), ->)
      && p^(-1)_h (R) edge("dd", "-[]") edge("ur", [h]_R, ->) \
      & W edge(f, ->) edge("dr", id_W, ->) & X edge("dr", id_X, ->) &
      & p^(-1)_(g compose f) (p^(-1)_h (R)) edge("ur", [g compose f]_(p^(-1)_h (R)), ->)
      edge("ull", [f, g]^(-1)_(p^(-1)_h (R)), <-, label-side: #left, label-pos: #25%, crossing: #true)
      & & Z \
      && W edge(f, ->) edge("uu", "[]-", shift: #(-4pt), crossing: #true) edge("drr", id_W, ->, label-pos: #60%)
      & X edge("rr", g, ->) && Y edge("ur", h, ->) \
      & & & & W edge("uu", "[]-", crossing: #true) edge("ur", g compose f, ->)
    $,
  ))]

which is exactly what we wanted.

We can therefore define $ Phi(p) = p^(-1) $

== Action of $Phi$ on morphisms

Let $p : cal(E)_1 arrow cal(B)$ and $q : cal(E)_2 arrow cal(B)$ be two fibrations, and
$F : p arrow q$ be a morphism
#align(center)[#diagram(
  spacing: 2cm,
  $
    cal(E)_1 edge(F, ->) edge("d", p, ->) & cal(E)_2 edge("d", q, ->) \
             cal(B) edge(id_(cal(B)), ->) & cal(B)
  $,
)]
We want to define $nu^F : p^(-1) arrow q^(-1)$.  Let $X : cal(B)$, $ nu^F_X & : & p^(-1)(X) & arrow.long q^(-1)(X) \
       &   &         S & mapsto.long F(S) \
       &   &         f & mapsto.long F(f) $
Which is well defined because, if $p(S) = X$, then $ q(F(S)) = p(S) = X $ and if
$f : S arrow R$ is in the fiber above $X$, then $ q(F(f)) = p(f) = id_X $ so $F(f)$
also lives in the fiber above $X$.  $nu^F_X$ is clearly functorial, because $F$ is.

Now, let $f : X arrow Y$ in $cal(B)$ $ nu^F_f (R) : q^(-1)_f (F(R)) arrow.long F(p^(-1)_f (R)) $
is defined by noting that we have the following commuting diagram
#align(center)[#diagram(
  spacing: 2cm,
  $
    p^(-1)_f (R) edge("d", "-[]") edge([f]_R, ->) & R edge("d", "-[]") \
                                    X edge(f, ->) & Y
  $,
)]
and so, by cartesianity of $F([f]_R)$, which stems from that of $[f]_R$ because $F$ preserves
cartesianity,
#align(center)[#diagram(
  spacing: 2cm,
  $
    q_f^(-1) (F(R)) edge("ddr", "-[]", bend: #(-30deg)) edge("drr", [f]_(F(R)), ->, bend: #30deg)
    edge("dr", nu^F_f (R), ->, "dashed") \
                                         & F(p^(-1)_f (R)) edge("d", "-[]") edge(F([f]_R), ->) & F(R) edge("d", "-[]") \
                                         & X edge(f, ->)                                       &                     Y
  $,
)]

=== $nu^F_f$ is an isomorphism
==== Naturality

#lemma[
  $nu^F_f$ is a natural transformation.
]
#proof[
  Let $g : R arrow S$ be a morphism in $p^(-1)_Y$.
  #align(center)[#diagram(
    spacing: 1.5cm,
    crossing-thickness: 5,
    $
      & F(R) edge("dd", F(g), ->, label-pos: #70%) \
      q^(-1)_f (F(R)) edge("ur", [f]_(F(R)), ->) edge("rr", nu^F_f (R), ->, crossing: #true, label-pos: #20%) edge("dd", q^(-1)_f (F(g)), ->)
      && F(p^(-1)_f (R)) edge("dd", F(p^(-1)_f (g)), ->) edge("ul", F([f]_R), ->) \
      & F(S) edge("dd", "-[]") \
      q^(-1)_f (F(S)) edge("rr", nu^F_f (S), ->, crossing: #true, label-pos: #30%) edge("ur", [f]_F(S), ->) edge("dd", "-[]")
      && F(p^(-1)_f (S)) edge("ul", F([f]_R), ->) edge("dd", "-[]") \
      & Y & \
      X edge("rr", id_X, ->) edge("ur", f, ->) && X edge("ul", f, ->)
    $,
  )]
  We have to show that the upper front square commutes.  This stems from the fact that
  $q_f^(-1)(F(g))$ has the universal property of living in the fiber over $X$, and making the
  left-most square commute, so we just need to check that the same is true for $ nu^F_f (S)^(-1) compose F(p_f^(-1)(g)) compose nu^F_f (R) $
  which is true because the two triangles and the right-most square commute in the above diagram.
]

==== Coherences
#lemma[
  $nu^F$ is a morphism.
]
#proof[
  We have shown that, for any $f$, $nu^F_f$ is a natural transformation.  We just have to
  check that $nu^F$ satisfies the coherence conditions.

  - Let $X : cal(B)$.  Let $R : p^(-1)_X$.
    We have to check that $ id_(nu_X (R)) = (nu^F_X ([id_X]_R)) compose nu^F_(id_X) (R) compose [id_X]_(nu_X (R))^(-1) $
    that is, $ [id_X]_(F(R)) = F([id_X]_R) compose nu^F_(id_X) (R) $
    which is, in diagrammatic form,
    #align(center, diagram(
      spacing: 2cm,
      $
        q^(-1)_(id_X) (F(R)) edge("d", nu^F_(id_X) (R), ->) edge("dr", [id_X]_(F(R)), ->) \
                            F(p^(-1)_(id_X)(R)) edge(F([id_X]_R), ->, label-side: #right) & F(R)
      $,
    ))
    the commutation of this diagram is exactly the definition of $nu^F_(id_X)(R)$.
  - Let $X,Y,Z : cal(B)$ be three objects, $f : X arrow Y$ and $g : Y arrow Z$ be two morphisms
    in $cal(B)$.  Let $R : p^(-1)_Z$.  We have to check that $ nu^F_(g compose f) (R) = nu^F_X ([f, g]^(-1)_R) compose nu^F_f (p^(-1)_g (R))
    compose q^(-1)_f (nu^F_g (R)) compose [f,g]'_(nu^F_Z (R)) $
    that is, that the following diagram commutes
    #align(center, diagram(
      spacing: 2cm,
      $
                   q^(-1)_(g compose f) (F (R))
                   edge([f, g]'_(nu^F_Z (R)), ->)
                   edge("dd", nu^F_(g compose f) (R), ->) & q^(-1)_f (q^(-1)_g (F(R)))
                                                            edge("d", q^(-1)_f (nu^F_g (R)), ->) \
                                                          & q^(-1)_f (F(p^(-1)_g (R)))
                                                            edge("d", nu^F_f (p^(-1)_g (R)), ->) \
        F(p^(-1)_(g compose f) (R)) edge(F([f, g]_R), ->) & F(p^(-1)_f (p^(-1)_g (R)))
      $,
    ))

    $nu^F_(g compose f) (R)$ is defined as the unique map in the fiber above $X$ that makes
    the following diagram commute
    #align(center, diagram(
      spacing: 2cm,
      $
        q^(-1)_(g compose f) (F(R)) edge("d", nu^F_f (R), ->) edge("dr", [g compose f]_(F(R)), ->) \
                      F(p^(-1)_(g compose f) (R)) edge(F([g compose f]_R), ->, label-side: #right) & F(R)
      $,
    ))
    Hence, we just need to show that the following diagram commutes
    #align(center, diagram(
      spacing: 2cm,
      $
        q^(-1)_(g compose f) (F(R)) edge([g compose f]_(F(R)), ->) edge("d", [f, g]'_(F(R)), ->)
        & F(R) \
        q^(-1)_f (q^(-1)_g (F(R))) edge("d", q^(-1)_f (nu^F_g (R)), ->)
        & F(p^(-1)_(g compose f)(R))edge("u", F([g compose f]_R), ->) \
        q^(-1)_f (F(p^(-1)_g (R))) edge(nu^F_f (p^(-1)_g (R)), ->)
        & F(p^(-1)_f (p^(-1)_g (R))) edge("u", F([f,g]_R^(-1)), ->)
      $,
    ))
    Indeed, we can fill it with commuting diagrams as follows
    #align(center, diagram(
      spacing: 2.5cm,
      $
        q^(-1)_(g compose f) (F(R)) edge("rrr", [g compose f]_(F(R)), ->) edge("dd", [f, g]'_(F(R)), ->)
        & & & F(R) \
        & q^(-1)_g (F(R)) edge("dr", nu^F_g (R), ->)
        edge("urr", [g]_F(R), ->)\
        q^(-1)_f (q^(-1)_g (F(R))) edge("d", q^(-1)_f (nu^F_g (R)), ->)
        edge("ur", [f]_(q^(-1)_g (F(R))), ->)
        & & F(p^(-1)_g (R)) edge("uur", F([g]_R), ->) & F(p^(-1)_(g compose f)(R)) edge("uu", F([g compose f]_R), ->) \
        q^(-1)_f (F(p^(-1)_g (R))) edge("urr", [f]_(F(p^(-1)_g (R))), ->) edge("rrr", nu^F_f (p^(-1)_g (R)), ->)
        & & & F(p^(-1)_f (p^(-1)_g (R))) edge("u", F([f,g]_R^(-1)), ->, label-side: #right) edge("ul", F([f]_(p^(-1)_g (R))), ->)
      $,
    ))
]

==== Iso
#lemma[
  $nu^F_f (R)$ is an isomorphism.
]
#proof[
  This stems from the fact that $[f]_(F(R))$ is cartesian.
]

We therefore define $ Phi(F) = nu^F $

= Grothendieck construction <grothendieck-construction>

In this section, we will define a functor $Psi : Pfct(cal(B)) arrow Fib(cal(B))$.

== Action of $Psi$ on objects

Let $cal(P) : cal(B)^(op) arrow Cat$ be a pseudo-functor. Let's build a fibration over $B$ out of
it.
#definition([Total category])[
  The total category $integral cal(P)$ has
  - objects: pairs $(X, x)$ with $X : cal(B)^(op)$ and $x : cal(P)_X$;
  - morphisms between two objects $(A, a)$ and $(B, b)$: pairs $(f_1, f_2)$ with $f_1 : A arrow B$
    in $cal(B)$ and $f_2 : a arrow cal(P)_f_1 (b)$.
  - identities for $(X, x) : integral cal(P)$: $(id_((X,x)))_0 = id_X$ and $ (id_((X,x)))_1 & : x arrow.long cal(P)_(id_X)(x) \
    (id_((X,x)))_1 & = i_X^(-1) (x) $

  - composition, given $(A, a), (B, b), (C, c) : integral cal(P)$, $(f_1,
      f_2) : (A, a) arrow (B, b)$ and $(g_1, g_2) : (B, b) arrow (C, c)$: $(h_1, h_2) =
    (g_1, g_2) compose (f_1, f_2)$ by
    - #box(width: 100%)[$h_1 : A arrow C = g_1 compose f_1$]
    - $h_2 : a arrow cal(P)_(g_1 compose f_1) (c)$ by
      #align(center)[#diagram(
        $
          a edge(f_2, ->) & cal(P)_f_1 (b) edge(cal(P)_f_1 (g_2), ->) & cal(P)_f_1 (cal(P)_g_1 (c))
          edge(c_(f_1, g_1)^(-1) (c), ->) & cal(P)_(g_1 compose f_1) (c)
        $,
      )]
]

#lemma()[
  Let $f$ be an isomorphism in $integral cal(P)$.  $f_1$ and $f_2$ are invertible.
]<iso-parts-iso>

#proof[
  Let $(f_1, f_2) : (A, a) arrow (B, b)$ a morphism in $integral cal(P)$, and
  $(g_1, g_2) : (B, b) arrow (A, a)$ such that $ (f_1, f_2) compose (g_1, g_2) & = id_(B, b) \
  (g_1, g_2) compose (f_1, f_2) & = id_(A, a) $
  We have that $f_1 compose g_1 = id_B$ and $g_1 compose f_1 = id_A$, so $f_1$ is invertible
  and $f_1^(-1) = g_1$.

  Furthermore, the following diagram commute
  #align(center, diagram(
    spacing: 2cm,
    $
      a edge(i_A (a)^(-1), ->) edge("d", f_2, ->) & cal(P)_(id_A) (a) \
      cal(P)_(f_1)(b) edge(cal(P)_(f_1)(g_2), ->)
      & cal(P)_(f_1) (cal(P)_(f_1^(-1)) (a)) edge("u", c_(f_1, f_1^(-1)) (a)^(-1), ->)
    $,
  ))
  So we have a candidate for the inverse of $f_2$, namely, $ hat(f)_2 := i_A (a) compose c_(f_1, f_1^(-1))^(-1) (a) compose cal(P)_(f_1)(g_2) $
  because the diagram above states that $hat(f)_2 compose f_2 = id_a$.  Furthermore,
  the following diagram commutes
  #align(center, diagram(
    spacing: 2cm,
    $
      b edge(i_B (b)^(-1), ->) edge("d", g_2, ->) & cal(P)_(id_B) (b) \
      cal(P)_(f_1^(-1))(a) edge(cal(P)_(f_1^(-1))(f_2), ->)
      & cal(P)_(f_1^(-1)) (cal(P)_(f_1) (b)) edge("u", c_(f_1^(-1), f_1)^(-1) (b), ->)
    $,
  ))
  Hence so does its image by $cal(P)_(f_1)$
  #align(center, diagram(
    spacing: 2cm,
    $
      cal(P)_(f_1)(b) edge(cal(P)_(f_1)(i_B (b)^(-1)), ->) edge("d", cal(P)_(f_1)(g_2), ->)
      & cal(P)_(f_1)(cal(P)_(id_B) (b)) \
      cal(P)_f_1(cal(P)_(f_1^(-1))(a)) edge(cal(P)_(f_1)(cal(P)_(f_1^(-1))(f_2)), ->)
      & cal(P)_f_1(cal(P)_(f_1^(-1)) (cal(P)_(f_1) (b))) edge("u", cal(P)_f_1(c^(-1)_(f_1^(-1), f_1) (b)), ->)
    $,
  ))
  Thus the following diagram commutes (the other inner squares/triangles are coherence conditions)
  #align(center, diagram(
    spacing: 2cm,
    $
      cal(P)_(f_1)(b)
      edge(cal(P)_(f_1)(i_B (b))^(-1), ->) edge("d", cal(P)_(f_1)(g_2), ->)
      edge("rr", id_(cal(P)_f_1(b)), ->, bend: #30deg)
      & cal(P)_(f_1)(cal(P)_(id_B) (b))
      edge("d", cal(P)_f_1(c_(f_1^(-1), f_1) (b)), ->)
      edge(c^(-1)_(f_1, id_B), ->)
      & cal(P)_f_1 (b)
      edge("ddl", c_(id_A, f_1) (b), ->, label-side: #left)
      edge("dddl", id_(cal(P)_f_1(b)), ->, bend: #50deg) \
      cal(P)_f_1(cal(P)_(f_1^(-1))(a)) edge(cal(P)_(f_1)(cal(P)_(f_1^(-1))(f_2)), ->)
      edge("d", c_(f_1, f_1^(-1))(a)^(-1), ->)
      & cal(P)_f_1(cal(P)_(f_1^(-1)) (cal(P)_(f_1) (b)))
      edge("d", c_(f_1, f_1^(-1))(cal(P)_(f_1) (b))^(-1), ->) \
      cal(P)_(id_A) (a) edge(cal(P)_(id_A) (f_2), ->) edge("d", i_A (a), ->)
      & cal(P)_(id_A) (cal(P)_f_1 (b)) edge("d", i_A (cal(P)_f_1(b)), ->) \
      a edge(f_2, ->) & cal(P)_f_1 (b)
    $,
  ))
  the outermost diagram states precisely $ f_2 compose hat(f)_2 = id_(cal(P)_f_1 (b)) $
]

#definition([Forgetful fibration])[
  We can now define the forgetful fibration $ pi(cal(P)) & : & integral cal(P) & arrow.long cal(B) \
             &   &          (A, a) & mapsto.long A \
             &   &      (f_1, f_2) & mapsto.long f_1 $
  which is clearly functorial.
]

#lemma[
  The forgetful fibration is a fibration.
]

#proof[
  Let $A,B : cal(B)$, $f : A arrow B$ and $b : cal(P)_B$, ie we have the following diagram:
  #align(center)[#diagram(
    spacing: 3em,
    $
                    & (B, b) edge("d", "-[]") \
      A edge(f, ->) & B
    $,
  )]

  We can lift $f$ as
  #align(center)[#diagram(
    spacing: 2cm,
    $
      (A, cal(P)_f (b)) edge((f, id_(cal(P)_f (b))), ->) edge("d", "-[]") & (B, b) edge("d", "-[]") \
                                                            A edge(f, ->) & B
    $,
  )]

  Hence, we just have to show that $(f, id_(cal(P)_f (b)))$ is cartesian.  Let $X : cal(B)$, $x :
  X$, $(g_1, g_2) : (X, x) arrow (B, b)$ and $h : X arrow A$ such that $g_1 = f compose h$:

  #align(center)[#diagram(
    spacing: 3em,
    $
      X edge("dr", g_1, ->) edge("d", h, ->) \
                               A edge(f, ->) & B
    $,
  )]
  We have to show there is a unique $hat(h) : x arrow cal(P)_h (cal(P)_f (b))$ with

  #align(center)[#diagram(
    spacing: 2cm,
    $
      x edge("r", g_2, ->) edge("d", hat(h), ->) & cal(P)_g_1 (b) \
      cal(P)_h (cal(P)_f (b)) edge(cal(P)_h (id_(cal(P)_f (b))), ->)
      & cal(P)_f (cal(P)_h (b)) edge("u", c^(-1)_(f, g) (b), ->)
    $,
  )]

  which is equivalent to the following diagram commuting

  #align(center)[#diagram(
    spacing: 2cm,
    $
                                             & cal(P)_h (cal(P)_f (b)) \
      x edge("ur", hat(h), ->) edge(g_2, ->) & cal(P)_(g_1) (b) edge("u", c_(f,g) (b), ->)
    $,
  )]

  but it is obvious that there is exactly one $hat(h)$ that makes this commute, namely, $ hat(h) = c_(f,g) (b) compose g_2 $
]

#lemma()[
  Let $(f_1, f_2)$ be a morphism in $integral cal(P)$.  $f_2$ is an isomorphism.
] <f2-iso>
#proof()[
  Let $(f_1, f_2) : (A, a) arrow (B, b)$.  In the previous proof, we have established
  that $(f_1, id_(cal(P)_f_1 (b)))$ is cartesian.  Hence, there exists a unique
  isomorphism $(id_A, phi)$ making the following diagram commute
  #align(center, diagram(
    spacing: 2cm,
    $
      (A, cal(P)_f_1 (b)) edge("dr", (f_1, id_(cal(P)_f_1(b))), ->)
      edge("d", (id_A, phi), ->, "dashed") \
               (A, a) edge((f_1, f_2), ->) & (B, b)
    $,
  ))
  hence the top square of this diagram commutes
  #align(center, diagram(
    spacing: 2cm,
    $
      cal(P)_f_1(b) edge("d", phi, ->) edge(id_(cal(P)_f_1(b)), ->)
      & cal(P)_f_1(b) edge("d", c_(id_A, f_1), ->)
      edge("dd", id_(cal(P)_f_1 (b)), ->, bend: #60deg)\
      cal(P)_(id_A) (a) edge(cal(P)_id_A (f_2), ->) edge("d", i_A (a), ->)
      & cal(P)_id_A (cal(P)_f_1 (b)) edge("d", i_A (cal(P)_f_1(b)), ->) \
      a edge(f_2, ->) & cal(P)_f_1(b)
    $,
  ))
  the lower square commutes by naturality of $i_A$, and the triangle commutes by a
  coherence condition.  Therefore, $ f_2 compose i_A (a) compose phi = id_(cal(P)_f_1(b)) $
  By @iso-parts-iso, $(id_A, phi)$ is an isomorphism, so $phi$ is too and hence $ f_2 = (i_A (a) compose phi)^(-1) $
  so $f_2$ is an isomorphism.
]

We thus define $Psi$ on objects by $ Psi(cal(P)) = (integral cal(P), pi(cal(P))) $

== Action of $Psi$ on morphisms

Let $cal(P)$, $cal(P)'$ be two pseudo-functors, and $nu : cal(P) arrow cal(P)'$ a morphism in
$Pfct(cal(B))$.

#definition[
  Let $ F_nu & : & integral cal(P) & arrow.long integral cal(P)' \
       &   &          (X, x) & mapsto.long (X, nu_X (x)) \
       &   &      (f_1, f_2) & mapsto.long (f_1, nu_(f_1) (b)^(-1) compose nu_X (f_2)) $

  That is, for $(f_1, f_2) : (A, a) arrow (B, b)$, we have
  #align(center, diagram(
    spacing: 3cm,
    $
      nu_X (a) edge(nu_A (f_2), ->) edge("dr", (F_nu (f_1, f_2))_2, ->, label-side: #right)
      & nu_A (cal(P)_(f_1) (b)) edge("d", nu_(f_1)(b)^(-1), ->) \
      & cal(P)'_(f_1) (nu_B (b))
    $,
  ))
]

#lemma[$F_nu$ is a fibration morphism]
#proof[
  We have to show that it makes the following diagram commute
  #align(center, diagram(
    spacing: 2cm,
    $
      integral cal(P) edge("d", pi(cal(P)), ->) edge(F_nu, ->) & integral cal(P)' edge("d", pi(cal(P)'), ->) \
                                         cal(B) edge(id_B, ->) & cal(B)
    $,
  ))
  and that $F_nu$ preserves the cartisian morphisms.
  - Let's show the two functors agree:
    - on objects: let $(X, x) : integral cal(P)$, $ pi(cal(P)') (F_nu (X, x)) & = pi(cal(P)') (X, nu_X (x)) \
                                & = X \
                                & = pi(cal(P))(X, x) $
    - on morphisms: let $(f_1, f_2) : (A, a) arrow (B, b)$, $ pi(cal(P)') (F_nu (f_1, f_2)) & = pi(cal(P)') ((f_1, nu_(f_1) (b)^(-1) compose nu_A (f_2))) \
                                    & = f_1 \
                                    & = pi(cal(P))(f_1, f_2) $
    Hence the diagram commutes.
  - Let $(f_1, f_2) : (A, a) arrow (B, b)$ be a cartesian morphism in $integral cal(P)$.  Let
    $(g_1, g_2) : (C, c) arrow (B, nu_B (b))$ be a morphism in $integral cal(P)'$ and $h_1 : C arrow B$
    in $cal(B)$ such that the following diagram commutes
    #align(center, diagram(
      spacing: 2cm,
      $
        C edge("d", h_1, ->) edge("dr", g_1, ->) \
                                 A edge(f_1, ->) & B
      $,
    ))

    Let's show that there exists a unique $h_2 : c arrow cal(P)'_h_1 (a)$ such that
    #align(center, diagram(
      spacing: 4cm,
      $
                                  (C, c) edge("dr", (g_1, g_2), ->) edge("d", (h_1, h_2), ->) \
        (A, nu_A (a)) edge((f_1, nu_f_1 (b)^(-1) compose nu_A (f_2)), ->, label-side: #right) & (B, nu_B (b))
      $,
    ))
    that is
    #align(center, diagram(
      spacing: 2cm,
      $
        c edge(g_2, ->) edge("dd", h_2, ->)
        & cal(P)'_g_1 (nu_B (b)) edge("d", c'_(h_1, f_1) (nu_B (b)), ->, label-side: #left) \
        & cal(P)'_h_1 (cal(P)'_f_1 (nu_B (b))) edge("d", cal(P)'_h_1 (nu_f_1 (b)), ->, label-side: #left) \
        cal(P)'_h_1 (nu_A (a)) edge(cal(P)'_h_1 (nu_A (f_2)), ->)
        & cal(P)'_h_1(nu_A (cal(P)_f_1 (b)))
      $,
    ))

    By @f2-iso, $f_2$ is an isomorphism, hence the commutation of the latter diagram is
    equivalent to that of the following, for which there clearly exists a unique $h_2$
  #align(center, diagram(
    spacing: 2cm,
    $
      c edge(g_2, ->) edge("dd", h_2, ->)
      & cal(P)'_g_1 (nu_B (b)) edge("d", c'_(h_1, f_1) (nu_B (b)), ->, label-side: #left) \
      & cal(P)'_h_1 (cal(P)'_f_1 (nu_B (b))) edge("d", cal(P)'_h_1 (nu_f_1 (b)), ->, label-side: #left) \
      cal(P)'_h_1 (nu_A (a)) edge(cal(P)'_h_1 (nu_A (f_2^(-1))), <-)
      & cal(P)'_h_1(nu_A (cal(P)_f_1 (b)))
    $,
  ))
  // Attempt:
  // #align(center, diagram(spacing: 2cm, $

  // $))

  // Attempt:
  // #align(center, diagram(spacing: 2cm, $
  //     c edge(g_2, ->) edge("dd", h_2, ->)
  //         & cal(P)'_g_1 (nu_B (b))
  //         edge("d", c'_(h_1, f_1) (nu_B (b)), ->, label-side: #left)
  //         edge(nu_g_1 (b), ->)
  //         & nu_A (cal(P)_g_1 (b))
  //         edge("dd", nu_A (c_(h_1, f_1) (b)), ->, label-side: #left) \

  //         & cal(P)'_h_1 (cal(P)'_f_1 (nu_B (b)))
  //         edge("d", cal(P)'_h_1 (nu_f_1 (b)), ->, label-side: #left) \
  //         cal(P)'_h_1 (nu_A (a)) edge(cal(P)'_h_1 (nu_A (f_2)), ->)
  //         edge("dr", nu_h_1 (a), ->, label-side: #right)
  //         & cal(P)'_h_1(nu_A (cal(P)_f_1 (b)))
  //         & nu_A (cal(P)_h_1 (cal(P)_f_1 (b)))
  //         edge("l", nu_h_1 (cal(P)_f_1(b)), <-) \
  //         & nu_A (cal(P)_h_1 (a)) edge("ur", nu_A (cal(P)_h_1 (f_2)), ->, label-side: #right)
  // $))

  // Nice but false:
  // $(f_1, f_2)$ is cartesian, hence invertible TODO, and by @iso-iff-parts-iso, $f_2$ is invertible,
  // hence the above diagram commuting is equivalent to the following one
  // #align(center, diagram(spacing: 2cm, $
  //     c edge(g_2, ->) edge("dd", h_2, ->)
  //         & cal(P)'_g_1 (nu_B (b)) edge("d", c'_(h_1, f_1) (nu_B (b)), ->, label-side: #left) \

  //         & cal(P)'_h_1 (cal(P)'_f_1 (nu_B (b))) edge("d", cal(P)'_h_1 (nu_f_1 (b)), ->, label-side: #left) \
  //         cal(P)'_h_1 (nu_A (a)) edge(cal(P)'_h_1 (nu_A (f_2^(-1))), <-)
  //         & cal(P)'_h_1(nu_A (cal(P)_f_1 (b)))
  // $))
  // which clearly has a unique solution for $h_2$.
]

= The equivalence <equivalence>

== $Phi compose Psi$
Let $cal(P) : cal(B)^(op) arrow Cat$ be a pseudo-functor.
#definition[
  Consider $ H^(cal(P)) & : & pi(cal(P))^(-1) & arrow.long cal(P) $
  defined by, for $X : cal(B)$, $ H^(cal(P))_X & : & pi(cal(P))^(-1)_X & arrow.long cal(P)_X \
               &   &            (X, x) & mapsto.long x \
               &   &         (id_X, f) & mapsto.long i_X (b) compose f $
  Let $(id_X, f) : (X, a) arrow (X, b)$ in $pi(cal(P))^(-1)_X$, that is,
  $f : a arrow cal(P)_(id_X) (b)$.  We have
  #align(center, diagram(
    spacing: 3cm,
    $
      a edge(f, ->) edge("dr", H^cal(P)_X (id_X, f), ->, label-side: #right)
      & cal(P)_id_X (b) edge("d", i_X (b), ->, label-side: #left) \
      & b
    $,
  ))
]

#lemma[
  $H^(cal(P))$ is a morphism in $Pfct(cal(B))$.
]
#proof[
  Let $f : X arrow Y$ in $cal(B)$, let's show that there is a natural isomorphism
  #align(center, diagram(
    spacing: 2cm,
    $
      pi(cal(P))^(-1)_Y edge(H^(cal(P))_Y, ->) edge("d", pi(cal(P))^(-1)_f, ->)
      & cal(P)_Y edge("d", cal(P)_f, ->) edge("dl", eta_f, =>) \
      pi(cal(P))^(-1)_X edge(H^(cal(P))_X, ->) & cal(P)_X
    $,
  ))
  Let $(Y, y) : pi(cal(P))^(-1)_Y$, that is, $y : cal(P)_Y$.  We have
  #align(center, diagram(
    spacing: 2cm,
    $
      pi(cal(P))^(-1)_f (Y, y) edge([f]_(Y, y), ->) edge("d", "-[]") & (Y, y) edge("d", "-[]") \
                                                       X edge(f, ->) & Y
    $,
  ))
  We can write $[f]_(Y,y) = (f, eta_f (y))$ with $eta_f (y) : H^cal(P)_X (pi(cal(P))^(-1)_f (Y, y)) arrow cal(P)_f (y)$.

  Let's prove that $eta_f$ is natural, and that it is an isomorphism.
  - #box(width: 100%)[let $y,y' : cal(P)_Y$ and $g : y arrow y'$. We want to show the the
      following diagram commutes]
    #align(center, diagram(
      spacing: 2cm,
      $
        H^cal(P)_X (pi(cal(P))^(-1)_f (Y, y)) edge(eta_f (y), ->)
        edge("d", H^cal(P)_X (pi(cal(P))^(-1)_f (id_Y, g)), ->)
        & cal(P)_f (y) edge("d", cal(P)_f (H^cal(P)_Y (id_Y, g)), ->, label-side: #left) \
        H^cal(P)_X (pi(cal(P))^(-1)_f (Y, y')) edge(eta_f (y'), ->) & cal(P)_f (y')
      $,
    ))
    We have that the following diagram commutes
    #align(center, diagram(
      spacing: 3cm,
      $
        pi(cal(P))^(-1)_f (Y, y') edge([f]_(Y, y'), ->) edge("dd", "-[]", bend: #(-50deg))
        & (Y, y') edge("dd", "-[]", bend: #50deg) \
        pi(cal(P))^(-1)_f (Y, y) edge([f]_(Y,y), ->) edge("d", "-[]") edge("u", pi(cal(P))^(-1)_f (id_Y, g), ->)
        & (Y, y) edge("d", "-[]") edge("u", (id_Y, g), ->, label-pos: #35%) \
        X edge(f, ->) & Y
      $,
    ))
    We can write $pi(cal(P))^(-1)_f (id_Y, g) = (id_Y, h)$, and so the commutation of the
    square implies the following commutation on the second component of the morphisms
    #align(center, diagram(
      spacing: 2cm,
      $
        H^cal(P)_X (pi(cal(P))^(-1)_f (Y, y)) edge(eta_f (y), ->) edge("d", h, ->) & P_f (y) edge("d", P_f (g), ->) \
      $,
    ))
  TODO
]

#lemma[$H^cal(P)$ is an isomorphism.]
#proof[TODO]

#lemma[$H^cal(P)$ is natural in $cal(P)$.]
#proof[TODO]

#lemma[
  $ Phi compose Psi tilde.equiv id_(Pfct(cal(B))) $
]
#proof[
  We have exhibited a natural isomophism $ H : Phi compose Psi arrow.double.long id_(Pfct(cal(B))) $
]

== $Psi compose Phi$
Let $p : cal(E) arrow cal(B)$ be a fibration.  $ Psi compose Phi (p) = pi(p^(-1)) : integral p^(-1) arrow cal(B) $

#definition[
  Consider $ G_p & : & integral p^(-1) & arrow.long cal(E) \
      &   &          (X, R) & mapsto.long R \
      &   &      (f_1, f_2) & mapsto.long [f_1]_R compose f_2 $
  Let $(f_1, f_2) : (X, S) arrow (Y, R)$, we have $f_1 : X arrow Y$ and $f_2 : S arrow p^(-1)_(f_1) (R)$
  #align(center, diagram(
    spacing: 2cm,
    $
      S edge("d", "-[]") edge(f_2, ->) & p^(-1)_(f_1) (R) edge("d", "-[]") edge([f_1]_R, ->) & R edge("d", "-[]") \
                      X edge(id_X, ->) & X edge(f_1, ->)                                     &                  Y
    $,
  ))
]

#lemma[
  $G_p$ is a fibration morphism.
]
#proof[TODO]

#lemma[$G_p$ is an isomorphism.]
#proof[TODO]

#lemma[$G_p$ is natural in $p$.]
#proof[TODO]

#lemma[
  $ Psi compose Phi tilde.equiv id_(Fib(cal(B))) $
]
#proof[
  We have exhibited the natural isomorphism $ G : Psi compose Phi arrow.double.long id_(Fib(cal(B))) $
]
This concludes the proof of the main theorem.

// Local Variables:
// tp--master-file: "/home/adri/dev/notes/notes.typ"
// End:
