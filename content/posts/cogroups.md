---
title: "Cogroups and Groups of Schemes"
date: 2020-08-01T11:08:13+02:00
display_image: '/cogroups/projective-line-pushout.png'
tags: ["Algerbaic Geometry", "Category theory", "cogroups"]
draft: false
---

`\(
\DeclareMathOperator{\Spec}{Spec}
\DeclareMathOperator{\C}{\mathbb{C}}
\DeclareMathOperator{\Z}{\mathbb{Z}}
\DeclareMathOperator{\Hom}{Hom}
\DeclareMathOperator{\Mod}{Mod}
\)`

# Introduction

I was watching Richard E. Borchards [lecture series on schemes](https://www.youtube.com/playlist?list=PL8yHsr3EFj50Un2NpfPySgXctRQK7CLG-) where he talked about groups in the category of schemes. Thinking about this I stumbled upon the idea of cogroups. I was already vaguely familiar with the idea of coalgebras, but I hadn't really looked at cogroups before (or so I thought). So this blogpost will just be my ramblings of what I found out.

Let's start at the beginning: a group in a category can be defined as an object `$G$` together with maps `$\mu: G \times G \to G$`, `$-1:G \to G$` and `$e:1 \to G$` making the following diagrams commute.

![Diagram of group axioms](/cogroups/group-axioms.png)

Here `$\times$` is the categorical product and `$1$` is the terminal object, so we have to assume or category has these. The diagrams describe the associativity, inverse and identity axioms respectively. You can check that if we apply this to the category of sets we get the standard definition of a group. If we take the duals of these diagrams, inverting the arrows, replacing `$\times$` by coproduct and `$1$` by the initial object we get the cogroup axioms.

Okay, so this is fun and all, but why care about cogroups? Well one reason might be the contravariant Yoneda embedding! Hang with me here. Let `$G$` be a cogroup in a category `$\mathcal{C}$`. If our Hom-functors preserve products and terminal objects (like they do in most the categories we know) then the Yoneda embedding makes `$\Hom(G, -)$` into a group in the functor category `$[\mathcal{C}, \mathbf{Set}]$`. This means that for any object `$X \in \mathcal{C}$` we have that `$\Hom(G, X)$` is a group in `$\mathbf{Set}$`. Further `$\Hom(G, -)$` lifts to a functor to the category of groups of sets, also known as `$\mathbf{Grp}$` the category of groups.

So cogroups give rise to functors to `$\mathbf{Grp}$`. In fact we're already familiar with a cogroup for this very reason. In the homotopy category of pointed topological spaces the `$n$`-sphere is a cogroup, and its Hom-functur is exactly the `$n$`th homotopy group. For `$n=1$`, the coproduct of the circle with itself is the figure eight, and the comultiplication is given by first going the first loop then the second. 

If you want to play a bit with this yourself you might try to figure out which (if any) cogroup gives rise to the following functors: The forgetful functor from `$\Mod R$` to `$\mathbf{Ab}$` sending a module to its underlying abelian group, the identity functor on `$\mathbf{Grp}$`, the inclusion of `$\mathbf{Ab}$` into `$\mathbf{Grp}$`.

Now let's go back to why I was looking at this in the first place. As you may or may not know the category of affine schemes is equivalent to the opposite category to the category of rings (for the purposes of this blogpost I will define rings to be commutative). Further the product of affine schemes coincides with their product in the category of schemes, so if we can understand functors from `$\mathbf{Ring}$` to `$\mathbf{Grp}$` as cogroups in `$\mathbf{Ring}$` this means we can extend them to the category of schemes!

Similar to the examples I listed above we have the functor giving the underlying additive group of a ring. This functor is given by a cogroup with object `$\Z[x]$`. The coproduct of `$\Z[x]$` with itself is `$\Z[x]\otimes \Z[x] = \Z[x,y]$`. The comultiplication maps `$x$` to `$x+y$`, the coinverse maps `$x$` to `$-x$`, and the counit maps `$x$` to `$0$`. It should make sense that this describes the additve group of a ring. 

Another important functor from rings to groups is the group of units. The idea is similar to that for the additive group but instead of using `$\Z[x]$` we use `$\Z[x^\pm] = \Z[x,y]/(xy-1)$`. Now we get a map from `$\Z[x^\pm]$` to `$R$` for every unit of `$R$` by mapping `$x$` to said unit. The comultiplication `$\Z[x^\pm] \to \Z[x^\pm, y^\pm]$` is given by `$x \mapsto xy$`, the coinverse by `$x \mapsto x^-$`, and the counit by `$x \mapsto 1$`.

Before we try to apply this to some schemes let's first simplify a little. `$\Z$` is way too complicated, so let us instead look at schemes over an algebraically closed field `$k$`. What this means is that in the definition of schemes every time the word ring appears we simply replace it with `$k$`-algebra instead. More formally what we do is take the \textit{over category} of schemes over `$\Spec k$`, but however you want to think about it this means that `$\Z$` is replaced by `$k$` and we don't have to think about prime numbers or anything difficult like that. 

Okay, onto the schemes. The only non-affine schemes I know anything about are projective spaces, so let's look at the projective line `$\mathbb{P}^1_k$`. The projective line is usually described with homogeneous coordinates `$(x:y)$`, where `$(x:y) = (\lambda x: \lambda y)$` for any `$\lambda \in k^\times$`, and `$x$` and `$y$` are not both 0. The homogeneous coordinates describe the closed points of `$\mathbb{P}^1_k$` and we also have a generic point. The regular functions of `$\mathbb{P}^1_k$` should come from regular functions on the affine plane that take the same value on `$(x, y)$` as `$(\lambda x, \lambda y)$`. If we restrict to coordinates of the form `$(1:y)$` we get polynomials of the form `$k[\frac{y}{x}]$` which is just an affine line. Similarly if we look at coordinates of the form `$(x:1)$` we get polynomials in  `$k[\frac{x}{y}]$`. The intersection of these are perhaps not surprisingly `$k[\frac{x}{y}, \frac{y}{x}]$`. Since this covers all the homogeneous coordinates we have described `$\mathbb{P}^1_k$` as a pushout of affine schemes.

![daf](/cogroups/projective-line-pushout.png)

This means we can understand morphisms `$\mathbb{P}^1_k \to \Spec R$` simply by looking at morphisms of affine schemes, and morphisms of affine schemes are just morphisms of `$k$`-algebras in the opposite direction (remember we're thinking of schemes over `$k$`). So what's the multiplicative group of the projective line? It's pairs of `$k$`-algebra maps `$k[x^\pm] \to k[\frac{x}{y}]$` and `$k[x^\pm] \to k[\frac{y}{x}]$` that coincides on `$k[\frac{x}{y}, \frac{y}{x}]$`. It should be clear that any such map sends `$x$` to a unit in `$k$` and it must be the same for both maps, so the unit group of `$\mathbb{P}^1_k$` is isomorphic to `$k^\times$`. 

Similarly for the additive group we just look at maps `$k[x] \to k[\frac{x}{y}]$` and `$k[x] \to k[\frac{y}{x}]$`. We see that for these to coincide on `$k[\frac{x}{y}, \frac{y}{x}]$` we need to map `$x$` to an element of `$k$`, so the additive group of `$\mathbb{P}^1_k$` is just the additive group of `$k$`.

Those where my ramblings, maybe I'll make a post in the future if I learn about any other schemes with interesting multiplicative/additive groups or if I find any other interesting groups of schemes.
