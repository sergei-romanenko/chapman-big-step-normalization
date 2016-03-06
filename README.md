# Agda formalizations of some big-step normalization proofs

This is a result of refactoring James Chapman's repository
<https://github.com/jmchapman/Big-step-Normalisation>,
whose README says:


> "This repo contains recently updated formalisations of BSN
(<http://cs.ioc.ee/~james/BSN.html>). There are three directories for
different calculi in each directory is an Everything.agda. The best
documentation for this is my this which you can find at the url above."

The purposes of the refactoring:

* To make some proof more human-friendly by exploiting the resources of the Standard Library (such as "equational reasoning").
* To rewrite the proof of soundness by replacing functions with
relations, in order to make Agda accept it. Now the horrible annotations
**{-# TERMINATING #-}** are not used any more. The original proof, however,
is easier to understand, and can be considered as a draft of the final proof.

## References

* Thierry Coquand and Peter Dybjer. 1997.
**Intuitionistic model constructions and normalization proofs.**
Mathematical. Structures in Comp. Sci. 7, 1 (February 1997), 75-94.
DOI=10.1017/S0960129596002150 <http://dx.doi.org/10.1017/S0960129596002150>

* Ana Bove and Venanzio Capretta. 2001.
**Nested General Recursion and Partiality in Type Theory.**
In *Proceedings of the 14th International Conference on Theorem Proving
in Higher Order Logics (TPHOLs '01)*,
Richard J. Boulton and Paul B. Jackson (Eds.).
Springer-Verlag, London, UK, UK, 121-135. 

* Thorsten Altenkirch and James Chapman. 2009.
**Big-step normalisation.**
J. Funct. Program. 19, 3-4 (July 2009), 311-333.
DOI=10.1017/S0956796809007278 <http://dx.doi.org/10.1017/S0956796809007278>

The idea to use OPEs (order-preserving embeddings) has been put forward in

* James Chapman. 2009. **Type Checking and Normalization.**
Ph.D. thesis, School of Computer Science, University of Nottingham.

and

* Andreas Abel and James Chapman. 2014.
**Normalization by evaluation in the delay monad: A case study for
coinduction via copatterns and sized types.**
In MSFP'14, volume 153 of EPTCS, pages 51--67.
<http://arxiv.org/abs/1406.2059v1>