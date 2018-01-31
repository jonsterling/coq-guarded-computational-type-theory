This is the Coq formalization of Sterling and Harper's "Guarded Computational
Type Theory".

# Hacking

To build this Coq development, ensure that you have Coq 8.7 installed. I
recommend that you install Coq in the standard way through
[OPAM](https://opam.ocaml.org/), and my instructions are not guaranteed to work
otherwise (they may work, but I have no way to double check).

    opam install coq.8.7.1+1

Now, you are ready to build this development. Simply run `make`. To build the
coqdoc (HTML rendering of the proofs), run `make html`.
