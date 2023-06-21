This GitHub repository pertains to the paper "RATIONAL POINTS ON RANK 2 GENUS 2 BIELLIPTIC CURVES IN THE LMFDB" by Francesca Bianchi and Oana Padurariu.

We first extract the genus 2 curves from the LMFDB whose automorphism group over Q contains C2 x C2. Their Jacobians are isogeous to a product of elliptic curves E1 x E2. In BiellipticGenus2List.m we store those curves for which rank(E1(Q))+rank(E2(Q)) = 2, where we also 
separate them into curves which have a rank 0 elliptic curve quotient (Rank0.m), and those that do not (allcurves.m).

We write some new functions to be able to process the database. They can be found in NewFunctions.m. 
The function BiellipticModel takes a curve from the database and returns an isomorphic model of the form y^2 = a6x^6+a4x^4+a2x^2+a0. We run this function over all the curves with no rank 0 quotient in the database. This is done in allcurves.m.

We pre-compute the set of three smallest primes of good ordinary reduction.

We take the extra cosets from the bielliptic quadratic Chabauty computation and we eliminate them using the Mordell-Weil sieve (MainCode.m). The Mordell-Weil sieve code is taken from https://github.com/steffenmueller/QCMod. To run the Mordell-Weil sieve over the database (or a subset of it), load MainCode.m in Magma.

Description of files:

* Bielliptic LMFDB: We consider all genus 2 curves C in the LMFDB whose automorphism group over Q contains C2 x C2 (automorphism group V4, D4, and D6, respectively). Then Jac(C) ~ E1 x E2 and we save those such that rk(E1(Q))+rk(E2(Q)) = 2.

* BiellipticGenus2List: All bielliptic genus 2 curves from the LMFDB such that Jac(C) ~ E1 x E2, with rk(E1(Q))+rk(E2(Q)) = 2. For each of them we find a bielliptic model y^2 = a6x^6+a4x^4+a2x^2+a0
and we separate them into those that admit a rank 0 quotient, and those that do not.

* OrderedLabels: We store the LMFDB labels, the number of known rational points on each curve, the coefficients of the bielliptic models, the conductors

* allcurves: We store the subset of curves taken from the LMFDB given by equations y^2 = f(x^2), with f of degree 3
whose Jacobians decompose up to isogeny as E1 x E2, where rk(E1(Q)) = rk(E2(Q)) = 1

* NewFunctions: "ellproj" projects points from J(Q) to E1(Q),E2(Q), "BiellipticModel" takes as input a genus 2 bielliptic curve and outputs a bielliptic model y^2 = f(x^2)

* Rank0: we deal with the subset of bielliptic curves admitting a rank 0 quotient

* fake_allcurves: we store the torsion information, the sizes of the Omega sets and the extra points from the QC computations that we are trying to eliminate

* allcurvesOutput: we store the smallest three primes of ordinary reduction, the sets of known points on all curves, the Mumford representations for generators of the free part of Jacobian, the Mumford representation for the torsion part of the Jacobian, the orders of generators for the torsion part. We need this information to run the QC code.
  
* MWSPrimes: we store the pre-computed mws_primes with respect to aux_int = 1, 2, 4. Not all primes will be needed in the MW sieve, the necessary ones will be stored in necessary_MWS_primes found in final_mws_primes

* sieve_with_no_known_points: Let X be a genus 2 bielliptic curve over Q, with no known point in X(Q).                                   This is a simple sieve to show that X(Q) = empty set, so QC is not necessary for this case. We apply this sieve to two curves in our database.

* TorsionStatistics: We count the number of curves whose Jacobians have torsion subgroups of order 1,2,3,4,5,6,respectively

* final_mws_primes: we store necessary MWS primes with respect to each element omega in Omega of each curve, and we consolidate this information in necessary_MWS_primes which stores the necessary MWS primes for each of the curves in the set
