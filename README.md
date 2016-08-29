
# hott-colimits

Formalization of properties of colimits in HoTT.

Files **Auxiliary.v**, **CommutativeSquares.v** and **Diagram.v** were written by Jeremy Avigad, Chris Kapulkin and Peter LeFanu Lumsdaine. They are from:

https://github.com/peterlefanulumsdaine/hott-limits/


* The file **Diagram.v** contains the definition of diagram, diagram morphisms, diagram equivalences and their inverse.

* The file **Colimit.v** contains the definitions of cocones and colimits, the HIT \texttt{colimit} and the proofs of functoriality and unicity.

* The file **Colimit_Sigma.v** contains the commutations commutation with sigmas, and **Colimit_Prod.v** the one with products.

* The file **CoEqualizer.v** we show that the HIT **Coeq** defined in the HoTT library is well a coequalizer for our definition of colimit.

* The files **Auxiliary.v**, **CommutativeSquares.v**, **MyLemmas.v** and **MyTacs.v** are auxiliary files.

* The files in **IteratedKernelPair** contain the formalization of the [slicing result](http://perso.eleves.ens-rennes.fr/~sboul434/documents/proof_slicing_result.pdf).


# Compilation

You need coq 8.5 and the HoTT library.
You have to precise the location of your `hoqc` in the files _CoqProject and .dir-locals.el (only for Proof General).
Then run:
     coq_makefile -f _CoqProject -o Makefile
     make

The compilation takes several minutes on my laptop.