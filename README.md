## Coalgebras for a functor

This project requires learning the basics of category theory and using
[Agda's categories library](https://github.com/agda/agda-categories).

The basic task is to:

- [x] define `F`-coalgebras and morphisms (alrady in the categories library)
- [x] show that they form a category
- [x] define polynomial functors on `Set` in one variable
- [x] define final `F`-coalgebras in terms of their universal property
- [x] show that polynomial functors have final coalgebras

Possible extensions:

* perform the construction more generally in a suitably nice category `𝒞`
* also define coalgebras for a comonad, with examples

### Suggested background reading materials

* Chapter 10 of Category Theory (Awodey)
  (https://www.andrew.cmu.edu/course/80-413-713/notes/chap10.pdf)

  - Section 10.5 gives an overview of algebras for endofunctors,
    Lambek's lemma, polynomial functors and existence of their
    initial algebras

  - to show the existence of the initial algebras of polynomial
    functors, you can in first instance use the existence of
    initial algebras in Agda; and later show this existence
    also via the (co-)continuitiy of polynomial functors)

