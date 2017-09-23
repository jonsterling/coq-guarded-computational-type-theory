# Hacking

To build this Coq development, ensure that you have Coq 8.6 installed. I
recommend that you install Coq in the standard way through
[OPAM](https://opam.ocaml.org/), and my instructions are not guaranteed to work
otherwise (they may work, but I have no way to double check).

    opam install coq.8.6


Next, we need to install `ssreflect`; we use the `ssreflect` plugin because it
provides generally superior tacticals, but we don't use any of the
`ssreflect`-related mathematical libraries at this point. This plugin should
also be installed through OPAM.


    opam repo add coq-released https://coq.inria.fr/opam/released
    opam install coq-mathcomp-ssreflect.1.6.1


Now, you are ready to build this development. Simply run `make`. To build the
coqdoc (HTML rendering of the proofs), run `make html`.


