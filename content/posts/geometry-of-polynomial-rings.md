---
title: "The Geometry of Polynomial Rings"
date: 2020-07-14T10:19:23+02:00
display_image: '/polynomial-rings/specR[x].png'
tags: ["Algerbaic Geometry", "Polynomial rings"]
draft: false
---

`\(
\DeclareMathOperator{\Spec}{Spec}
\DeclareMathOperator{\C}{\mathbb{C}}
\)`

Inspired by Ravi Vakil's summer project about algebraic geometry I wanted to make this blog post about the spectrum of polynomial rings and how to conceptualize them geometrically when your field isn't algebraically closed. 

The spectrum of a ring `$R$`, denoted `$\Spec R$`, is the set of all prime ideals of `$R$` (with some additional structure). We think of a `$\Spec R$` as a geometric space where the points are the maximal ideals, and the prime ideals contained in a maximal ideal represent geometric objects containing the point. 

As an example, think of `$\Spec \C[x, y]$`: the maximal ideals are of the form `$(x-a, y-b)$`, and we can think of this as a point `$(a,b) \in \C^2$`. The other prime ideals of `$\Spec \C[x, y]$` are the irreducible polynomials, and `$(0)$`. We can think of the irreducible polynomials as "curves" in `$\C^2$`, for example we think of `$(y - x^2)$` as the curve where `$y=x^2$`. You can verify that `$(x-a, y-b)$` contains `$(y - x^2)$` if and only if `$b=a^2$`, so this matches our intuition for the geometry of `$\C^2$`. Lastly since every ideal contains `$(0)$` it represents the entire plane.

In general when `$k$` is an algebraically closed field the points of `$\Spec k[x_1, \cdots, x_n]$` are exactly the points of `$k^n$`. Let's warm up by proving this fact.

# Hilbert's weak nullstellensatz
Noether's normalization lemma states that if `$A$` is a finitely generated commutative `$k$`-algebra, then there is a finitely generated subalgebra `$B \subseteq A$` such that `$A$` is a finite `$B$`-module, and `$B$` is a free commutative `$k$`-algebra. In other words `$B$` is isomorphic to a polynomial ring in a finite amount of variables. I will assume this as known, but a proof is available at for example [Wikipedia](https://en.wikipedia.org/wiki/Noether_normalization_lemma).

We can use Noether's normalization lemma to understand the maximal ideals of `$A := k[x_1, \cdots, x_n]$`. Say `$\mathfrak{m}$` is a maximal ideal of `$A$`. Then `$A/\mathfrak{m}$` is a finitely generated `$k$`-algebra which is also a field. Applying Noether normalization we see that `$A/\mathfrak{m}$` has a free subalgebra `$B$`. Let `$B_{(0)}$` be the field of fractions of `$B$` contained in `$A/\mathfrak{m}$`. Since finitely generated algebras over `$k$` are Noetherian and `$A/\mathfrak{m}$` is a finitely generated `$B$`-module, it follows that `$B_{(0)}$` is a finitely generated `$B$`-module. This must imply that `$B=k$`, because for all other free `$k$`-algebras there field of fractions are infinitely generated. In conclusion `$A/\mathfrak{m}$` must be a finite field extension of `$k$`.

If we further assume that `$k$` is algebraically closed the only finite extension of `$k$` is `$k$` itself, so `$\mathfrak{m}$` is the kernel of a `$k$`-algebra homomorphism `$\varphi: A \to k$`. Then it is clear that `$\mathfrak{m} = \big(x_1 - \varphi(x_1), \cdots, x_n - \varphi(x_n)\big)$`. This allows us to associate the maximal ideals of `$A$` with points in `$k^n$`.

# Galois orbits
We turn our attention to what happens when `$k$` is not algebraically closed. `$A/\mathfrak{m}$` is still a finite extension of `$k$`, and since finite extensions are algebraic it embeds into `$K$`, the algebraic closure of `$k$`. In other words `$\mathfrak{m}$` is the kernel of a `$k$`-algebra homomorphism `$A \to K$`. So it seems like we can associate the maximal ideals with points in `$K^n$`, but unlike when `$k$` was algebraically closed there can be several homomorphisms with the same kernel, so this association is not unique. For example if we post-compose with any `$k$`-algebra automorphism of `$K$` we would get a different homomorphism with the same kernel. In fact we will see that this is the only thing you can do.

**Theorem**: If `$\varphi, \psi : A \to K$` are `$k$`-algebra homomorphisms from a polynomial algebra to the algebraic closure of `$k$` with the same kernel then there is a `$k$`-algebra automorphism of `$\alpha: K \to K$` such that `$\varphi = \alpha \psi$`.

*proof*: Let `$E$` be the image of `$\psi$` and `$E'$` the image of `$\varphi$`. Since they are both isomorphic to `$A/\text{ker}\varphi$` there is an isomorphism `$E \to E'$`. Let `$\tilde{\alpha}$` be the composition `$E \to E' \hookrightarrow K$` of the isomorphism with the inclusion of `$E'$`. Then I claim `$\tilde{\alpha}$` extends to a `$k$`-algebra automorphism of `$K$`. The proof uses Zorn's lemma.

Let `$P := \left\lbrace (F, \gamma) \mid E \subseteq F,\; \gamma:F \to K,\; \gamma|_E = \tilde{\alpha} \right\rbrace$` be the set of extensions of `$\tilde{\alpha}$` to field extensions of `$E$`. Define a partial order on `$P$` by `$(F, \gamma) \leq (F', \gamma')$` if `$F \subseteq F'$` and `$\gamma'|_F = \gamma$`. `$P$` is clearly non-empty since it contains `$E$`, further if `$\big((F_i, \gamma_i)\big)_{i\in I}$` is a chain in `$P$` then `$(F, \gamma)$` is an upper bound with `$F = \bigcup\limits_{i\in I} F_i$` and `$\gamma(x) = \gamma_i(x)$` whenever `$x$` is in `$F_i$`. Now applying Zorn's lemma we get that `$P$` has a maximal element `$(F, \alpha)$`. I claim that `$F = K$` and that `$\alpha$` is an automorphism.

Let `$a$` be any element of `$K$`. Since `$F \subseteq K$` is an algebraic extension `$a$` has a minimal polynomial `$p(x)$` with coefficients in `$F$`. We have that `$F(a) \simeq F[x]/(p(x))$`. Let `$F'$` denote the image of `$\alpha$`. Since `$\alpha$` is a homomorphism of fields it is an isomorphism onto its image and thus induces an isomorphism of rings `$\hat{\alpha}:F[x] \to F'[x]$`. Let `$a'$` be a root of `$\hat{\alpha}(p(x))$`, then `$F'(a') \simeq F'[x]/\hat{\alpha}(p(x)) \simeq F[x]/(p(x)) \simeq F(a)$`. Thus we can extend `$\alpha$` to `$F(a)$` by mapping `$a$` to `$a'$`. Since `$(F, \alpha)$` is maximal this implies that `$F=K$`. And since `$F'\simeq F = K$` is algebraically closed and `$K$` doesn't have any proper algebraic subfields `$\alpha$` is surjective. Therefor `$\alpha$` is an automorphism such that `$\varphi = \alpha \psi$`. □

So what does this mean? If we let `$G$` be the group of `$k$`-algebra automorphisms of `$K = \bar{k}$`, and we let `$G$` act diagonally on `$K^n$`. Then the maximal ideals of `$k[x_1, \cdots, x_n]$` are in bijection with the orbits of `$K^n$`. These orbits are called Galois orbits (even though there is no assumption that the extension `$k \to K$` is Galois).

# Geometric pictures

Let's use this knowledge to understand `$\Spec \mathbb{R}[x]$`. The real automorphisms of `$\C$` are the identity and complex conjugation, so `$\Spec \mathbb{R}[x]$` looks like `$\C$` modulo conjugation. It's the complex plane and fold it along `$\mathbb{R}$`, leaving us with the upper half plane `$\C^\geq$`. 

![The geometry of R`[x]`](/polynomial-rings/specR[x].png)

If we add more variables and look at for example `$\Spec \mathbb{R}[x, y]$` we get `$\C^> \times \C \cup \mathbb{R} \times \C^\geq$`, where `$\C^>$` is the strict upper half plane (i.e. not including `$\mathbb{R}$`). Since I have not yet learned to draw in four dimensions I leave you with this illustration of the imaginary component.

![The geometry of R`[x, y]`](/polynomial-rings/specR[x,y].png)

The maximal ideal corresponding to a point `$(z=a+bi, w=c+di) \in \C^> \times \C$` is `$\big((x-z)(x-\bar{z}), (xd - yb - (ad-bc))\big)$`, while the maximal ideal corresponding to `$(r, w) \in \mathbb{R} \times \C^\geq$` is `$\big((x-r), (y-w)\big)$` if `$w$` is real and `$\big((x-r), (y-w)(y-\bar{w})\big)$` if it is not. So the maximal ideals of `$\mathbb{R}[x, y]$` are those generated by an irreducible polynomial in one of the variables and a linear polynomial in both/the other variable.
