TLDR: To run the Mordell-Weil sieve over the database (or a submit of it), load MainCode.m in Magma.

We first extract the genus 2 curves from the LMFDB whose Jacobian have analytic rank 2 
and the automorphism group over Q contains C2 x C2. We store the set of curves in BiellipticGenus2List.m, where we also 
separate them into curves which have a rank 0 elliptic curve quotient, and those that do not. In the process we also 
provably show that the algebraic ranks of the Jacobians equal 2, by computing the ranks of the elliptic curves in 
the isogeny decomposition.

We write some new functions to be able to process the database. They can be found in NewFunctions.m. 
The function BiellipticModel takes a curve from the database and returns an isomorphic model of the form y^2 = a6*x^6+a4*x^4+a2*x^2+a0. We run this function over all the curves in the database with not rank 0 quotient. This is done in allcurves.m.

We pre-compute a set of three QC primes in FindPrimes.m.

We take the extra cosets from the bielliptic Quadratic Chabauty computation and we eliminate them using the Mordell-Weil sieve (MainCode.m).
