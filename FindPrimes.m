//code taken from https://github.com/steffenmueller/QCMod

//this function finds QC primes up to a bound
//we need three QC primes for each curve
function find_qc_primes(X : qc_primes_bound := 165, mws_primes_bound := 1000, ordinary := true, 
               printlevel := 0, number_of_bad_disks := 0, mws_quot_bd := 10, inf_modp_allowed := true , known_rat_pts := [])
  // X is a genus 2 curve over the rationals
  // Find good primes for quadratic Chabauty / Mordell-Weil sieve combination
  //
  // * ordinary: if true, only allow ordinary primes for qc 
  // * number_of_bad_disks: only look at primes for qc such that we have this number of
  //   Weierstrass pts mod p. In practice this is 0 or 1 (1 if we need an odd degree model
  //   mod p, to compute local heights at p for divisors) 
  // * mws_quot_bd controls the allowed quality of the mws-primes, i.e. the probability
  //   that we'll get nontrivial information from them
  // * if inf_modp_allowed is true, then we allow qc primes p such that there are
  //   p-adically rational points at infinity.
  //
  assert Genus(X) eq 2;
  f,h := HyperellipticPolynomials(X);
  assert IsZero(h);
  disc := Integers()!Discriminant(f);
  J := Jacobian(X);
  
  // Find good primes for the MWSieve
  if ordinary then 
    gops := [p : p in PrimesInInterval(3, qc_primes_bound) | is_good_ordinary(X, p)];
  else
    gops := [p : p in PrimesInInterval(3, qc_primes_bound)];
  end if;
  qc_primes := [p : p in gops | #Roots(ChangeRing(f, pAdicField(p))) eq number_of_bad_disks];
  if not inf_modp_allowed then  // want no rational points in disks at infinity
    qc_primes := [p : p in qc_primes | &and[Numerator(P[3]) mod p ne 0 : P in known_rat_pts]]; 
  end if;
  assert #qc_primes gt 0;
  good_primes := [v : v in PrimesInInterval(3, mws_primes_bound) | not IsDivisibleBy(disc, v)]; 
  number_of_primes := #good_primes;
  time groups := [AbelianGroup(BaseChange(J, GF(good_primes[i]))) : i in [1..number_of_primes]];
  prime_quality := [];
  // TODO: Sort in a more meaningful way. 
  for p in qc_primes do
    if printlevel gt 0 then "p", p; end if;
    _, quots := sieving_primes(p^10,  good_primes, groups, mws_quot_bd : printlevel := printlevel);
    if IsEmpty(quots) then 
      Append(~prime_quality, []);
    else 
      Append(~prime_quality, quots); // 
    end if;
  end for;
  //ParallelSort(~prime_quality, ~qc_primes);
  //prime_exponents := [Max([Valuation(Exponent(G), p) : G in groups]) : p in qc_primes];
    
  return qc_primes, groups, good_primes, prime_quality;
end function;