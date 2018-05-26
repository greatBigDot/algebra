# algebra

A representation of several basic algebraic structures (e.g., groups, rings, vector spaces) as Idris interfaces (axioms fully enforced).

Mathematically, the idea of an algebraic structure is quite simple. Consider
(a) the set of integers \\(\mathbb{Z}\\), (b) two of the most basic functions
on it, \\(+: \mathbb{Z}^2 \to \mathbb{Z} \\) and \\(\cdot: \mathbb{Z}^2 \to
\mathbb{Z}\\), and (c) two unique elements of it, \\(0\\) and \\(1\\). There
are various obvious properties that universally hold; e.g.:

* \\(x+(y+z) = (x+y)+z\\), and \\(x\cdot (y \cdot z) = (x \cdot y) \cdot z\\)
* \\(x+y= y+x\\), and \\(x\cdot y = y \cdot x\\)
* \\(x+0 = x \cdot 1 = x \\)
* \\(\exists~y\in \mathbb{Z} [ x+y = 0 ]\\)
* \\(x \cdot (y+z) = x \cdot y + x \cdot z\\)

(Unquantified variables are implicitly quantified over the domain of discourse,
\\(\mathbb{Z}\\).) These properties are referred to, respectively, as
**associativity**, **commutativity**, **identities**, **additive inverses**,
and **dsitributivity of (multiplication over addition)**. There are various
things to note. Plenty of other sets satisfy these laws; for example, the
rational numbers, or the real numbers, or the complex numbers. Note also that,
say, the irrational numbers do *not* satisfy these properties; \\(pi +
(1-\pi)\\) is rational, and so \\(+\\) isn't even a binary function over the
irrationals! Finally, note the asymmetry in the fourth law, an asymmetry not
present in the others. This is necessary, as the following property (referred
to as **multiplicative inverses**) does *not* hold:

* \\(\exists y \in \mathbb{Z} [ x \cdot y = 1 ]\\)

While \\(2\\), for example, *does* have a multiplicative inverse among the
*rationals*, it doesn't when we restrict our attention to the integers. (In
fact, not even the rational numbers satisfy the above law, because \\(0\\) does
not have a multiplicative inverse. After modifying the law to account for that
special case, however, the rationals do satisfy it, while the integers still
don't.)

So, was the point of all this? All we did was consider some numbers that
everyone is familiar with and mention some elementary properties of them. How
does that lead to any interesting mathematical questions? Well, the key idea,
the crucial motivating question of abstract algebra, is the following:

__*What happens when we go in the other direction?*__

That is, what happens when we *start* with a list of properties, then ask what
sorts of things satisfy it? The answers to this question are more diverse than
you may expect. For example, in addition to the integers and its extensions,
other more esoteric sets satisfy the above laws. E.g., the set of integers
modulo five, \\(\mathbb{Z}\_5 = \left\\{\overline{0}, \overline{1},
\overline{2}, \overline{3}, \overline{4}\right\\}\\). In the set, to calculate
the \"sum\" of two elements, we calculate their usual sum, then take that
modulo 5 (that is, the remainder when dividing by 5; the modulo operation is
essentially a generalization of the concept of even and odd numbers to
divisibilities other than by 2); similarly with the product. Thus, for example,
\\(\overline{4} + \overline{3} = \overline{2}\\). A similar line of reasoning
indicates that additive inverses exist\-\--in fact, so do multiplicative
inverses, at least for non-\\(0\\) elements! Observe:

* \\(\overline{1} \cdot \overline{1} = \overline{1}\\)
* \\(\overline{2} \cdot \overline{3} = \overline{1}\\)
* \\(\overline{3} \cdot \overline{2} = \overline{1}\\)
* \\(\overline{4} \cdot \overline{4} = \overline{1}\\)

However, if we look at the integers modulo 6 (\\(\mathbb{Z}\_6\\)), we find
that multiplicative inverses do *not* always exist; only \\(\overline{1}\\) and
\\(\overline\{-1} = \overline{5}\\) are invertible. (Try it!) In fact, the
integers modulo n, \\(\mathbb{Z}\_n\\), satisfy the weakened (i.e., ignoring
\\(0\\)) multiplicative inverse law if and only if \\(n\\) is prime.

These do not exhaust the possibilities\-\--not even close!\-\--but it should be
enough to give a taste of what abstract algebra is all about. You start with
some set with defined operations (a pairing known as a \"structure\") that you
are familiar with, you distill that structure down to its most basic and
fundamental properties, and then you look at what sorts of things satisfy those
properties and what those properties alone entail. This allows you to
generalize familiar structures to more abstract ideas\-\--the original
motivating structure becomes just a special case of a more general property,
and seemingly disparate things suddenly become two special cases of a more
general idea.

Note that in the process of generalization, we choose to \"forget\" any
auxiliary properties of the motivating structure. That is, the set of objects,
the binary functions \\(+\\) and \\(\cdot\\), and the privilleged elements
\\(0\\) and \\(1\\), are not necessarily numbers, addition, multiplication,
zero, or one (respectively)! They can be any mathematical object (that is, any
concept that can be precisely defined) satisfying the list of properties above.
In other words, they are *like* numbers with respect to the most basic
qualities of them, but they may in fact be completely different!

Thus, using the axioms as a starting point, one can ask which properties are
entailed by them, and which properties will differ between different
implementations of the axioms. What are the necessary and sufficient conditions
for various additional facts? E.g., does it follow from the laws above that
every element has a unique factorization? Among the motivating structure of the
integers this was true (a fact known as the Fundamental Theorem of Arithmetic);
in general, though, it is false! The question then becomes how to further
classify the space of implementations\-\--what's the simplest way to divide
those that do always admit a unique factorization and those that don't? These
are the kinds of questions that the framework of algebraic structures allows
you to ask.

The laws given above define a ring; that is, any set (with the two defined
binary operations over it, as well as the two distinguished elements (which can
be thought of as nullary operations for uniformity)) satisfying the above list
of properties is known as a __ring__. The laws are called the __ring axioms__.
__Ring theory__ is the branch of math studying rings, how they relate to each
other (namely, via __ring homomorphisms__), and how they relate to other
mathematical objects. Rings are not the only algebraic structure; there are
many, many more, and this package defines a few of the more important ones as
Idris interfaces, as well as some instances of that interface. Each module
contains in its documentation an overview of that algebraic structure and some
interesting properties of them that make them worth studying.

To create an instance of an algebraic structure's interface, one must not only
provide the sets and operations with the proper signatures, but also provide
proofs of the axioms of that algebraic structure. To see how this works, you
might want to take a look at `Algebra.Group`.
