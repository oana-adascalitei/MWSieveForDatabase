This GitHub repository pertains to the paper "RATIONAL POINTS ON RANK TWO BIELLIPTIC CURVES IN THE LMFDB" by Francesca Bianchi and Oana Padurariu.

We first extract the genus 2 curves from the LMFDB whose automorphism group over Q contains C2 x C2. Their Jacobians are isogeous to a product of elliptic curves E1 x E2. In BiellipticGenus2List.m we store those curves for which rank(E1(Q))+rank(E2(Q)) = 2, where we also 
separate them into curves which have a rank 0 elliptic curve quotient (Rank0.m), and those that do not (allcurves.m).

We write some new functions to be able to process the database. They can be found in NewFunctions.m. 
The function BiellipticModel takes a curve from the database and returns an isomorphic model of the form y^2 = a6x^6+a4x^4+a2x^2+a0. We run this function over all the curves with no rank 0 quotient in the database. This is done in allcurves.m.

We pre-compute the set of three smallest primes of good ordinary reduction.

We take the extra cosets from the bielliptic quadratic Chabauty computation and we eliminate them using the Mordell-Weil sieve (MainCode.m). The Mordell-Weil sieve code is taken from https://github.com/steffenmueller/QCMod. To run the Mordell-Weil sieve over the database (or a subset of it), load MainCode.m in Magma.
