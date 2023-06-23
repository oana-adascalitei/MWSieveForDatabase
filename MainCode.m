//the code is an adaptation of the Mordell-Weil sieve from 
//https://github.com/steffenmueller/QCMod

//we are computing data which is recorded in the json files:

//done_fake: we originally define it as done_fake := [[false : i in [1..#all_fake_coeffs[index][1]]]: index in [1..#all_fake_coeffs]]; 
//if the sieve is successful each boolean must become true

//done_pr: we originally define it as done_pr := [[[] : i in [1..#all_fake_coeffs[index][1]]]: index in [1..#all_fake_coeffs]];
//we have data from Sage concerning three primes of good ordinary reduction, done_pr records which subset of these primes 
//is necessary for a successful sieve together with the auxiliary integer. The modulus can be extracted from these data.

//necessary_pr: we record the necesarry primes used for the Mordell-Weil sieve. The pre-computed sets of MWS primes are quite
//large, but we will only need a subset of them


load "MWSieveCode.m";
load "allcurvesOutput.m";
load "allcurves.m";
load "fake_allcurves.m";
load "MWSPrimes.m";
//SetLogFile("done.log");
//SetLogFile("necessary_primes.log");
//SetLogFile("necessary_MWS_primes.log");
ExtraF1 := [ 109, 164, 300 ]; //trivial torsion where we use aux_int = 1,2,4
Failed := [];
N := 4; //exponents used in the modulus for all QC primes
R<x> := PolynomialRing(Rationals());
done_fake := [[false : i in [1..#all_fake_coeffs[index][1]]]: index in [1..#all_fake_coeffs]];
done_pr := [[[] : i in [1..#all_fake_coeffs[index][1]]]: index in [1..#all_fake_coeffs]];
necessary_pr := [[[] : i in [1..#all_fake_coeffs[index][1]]]: index in [1..#all_fake_coeffs]];
//we can run it over all the curves in the database, or some subset given by indices
//for index in [i : i in [1..10] | i in [295,333] eq false] do
for index in [i : i in [1..#allcurves] | i in [295,333] eq false] do
  print("Curve"),index; print allcurves[index]; print("Omega has size"),#all_fake_coeffs[index][1]; 
  X:=HyperellipticCurve(allcurves[index]);
  Pts := pts[index];
  base_pt := X!Pts[1]; 
  J:=Jacobian(X);
  AuxSet := [];
  //for non-trivial torsion we may have to use aux_int > 1
  if index in ExtraF1 cat T2 cat T4 then
    AuxSet := [2,4]; 
  end if;
  if (index in T3 and (3 in ordinary_pr[index] eq false)) or (index in T6 and (3 in ordinary_pr[index] eq false)) then
    AuxSet := [3]; 
  end if;
  //we pre-computed mws_primes with respect to aux_int in {1,2,4}, 
  //but for other values of aux_int we need to compute it here 
  if #[i : i in AuxSet | i in [1,2,4] eq false ] ge 1 then
    B := BadPrimes(X); 
    AA := 10^4;
    if index in LowerBound then
      AA := 10^3;
    end if;
    A := PrimesUpTo(AA); 
    A := [p: p in A | (p in B) eq false];
    groups := [];
    for i in [1..#A] do
      groups[i] := AbelianGroup(Jacobian(ChangeRing(X,GF(A[i]))));
    end for;
  end if; 
  torsion_orders := tor_ord[index];
  if torsion_orders eq [] then 
    torsion_bas := [];
  else 
    torsion_bas := [elt< J | tor_bas[index][i][1], tor_bas[index][i][2], 2 > : i in [1..#torsion_orders]];
  end if;
  bas := [];
  bas[1] := elt< J | gens[index][1][1], gens[index][1][2], 2 >;
  bas[2] := elt< J | gens[index][2][1], gens[index][2][2], 2 >;
  fake_all_om := all_fake_coeffs[index];
  //the extra points are partitioned with respect to the elements of Omega
  //each of #all_fake_coeffs[index][1], #all_fake_coeffs[index][2] and #all_fake_coeffs[index][3]
  //must have size OmegaSizes[index]
  assert #all_fake_coeffs[index][1] eq OmegaSizes[index];
  //we perform the sieve with respect to each element in Omega
  for om in [1..#all_fake_coeffs[index][1]] do
    "Omega",om,"out of",#all_fake_coeffs[index][1];
    fake := [fake_all_om[1][om],fake_all_om[2][om],fake_all_om[3][om]];
    //if there are no fake points for one of the QC primes, we can bypass the sieve
    if [] in fake then 
      print "easy";
      done_fake[index][om] := true;
      done_pr[index][om] := [0];
      continue;
    end if;
    for ind in [[1,2],[1,3],[2,3],[1,2,3]] do 
      ordinary_primes := [ordinary_pr[index][i] : i in ind ];
      print ordinary_primes;
      exponents := [N : p in ordinary_primes]; 
      ordinary_M := &*[ordinary_primes[i]^exponents[i] : i in [1..#ordinary_primes]]; //modulus prior to adding aux_int 
      aux_int := 1; //the default aux_int
      print "aux_int =", aux_int;
      M := ordinary_M*aux_int; // modulus after aux_int
      //pre-computed mws_primes
      mws_primes := MWSPrimes[index];
      mwsbool := IsEmpty(mws_primes);
      print("mws_primes");print mws_primes;
      fake_coeffs := [];
      for i in ind do
        Append(~fake_coeffs, [fake[i]]); 
      end for;
      printf "number of extra points: %o\n", [#fake[1],#fake[2],#fake[3]];
      ordinary_fake_coeffs_mod_M := coeffs_CRT(fake_coeffs, ordinary_primes, exponents);
      printf "number of cosets: %o\n", #ordinary_fake_coeffs_mod_M;
      fake_coeffs_mod_M := combine_fake_good(ordinary_fake_coeffs_mod_M, ordinary_M, aux_int);
      printf "after aux_int: %o\n", #fake_coeffs_mod_M;
      if #torsion_bas eq 0 then //if the torsion is trivial
        fake_coeffs_new := fake_coeffs_mod_M;
      end if;
      if #torsion_bas eq 1 then //if torsion is generated by one element
        fake_coeffs_new := [**];
        for k in [0..torsion_orders[1]-1] do
          for i in [1..#fake_coeffs_mod_M] do
            Append(~fake_coeffs_new, [*fake_coeffs_mod_M[i][1], fake_coeffs_mod_M[i][2], Integers()!k*]);
          end for;
        end for;
      end if;
      if #torsion_bas eq 2 then //if torsion is generated by two elements
        fake_coeffs_new := [**];
        for k1 in [0..torsion_orders[1]-1] do
          for k2 in [0..torsion_orders[2]-1] do
            for i in [1..#fake_coeffs_mod_M] do
              Append(~fake_coeffs_new, [*fake_coeffs_mod_M[i][1], fake_coeffs_mod_M[i][2], Integers()!k1,Integers()!k2*]);
            end for;
          end for;
        end for;
      end if;
      printf "after torsion: %o\n", #fake_coeffs_new;
      d_f,necessary_primes1,bool_list := MWSieve(J, mws_primes, M, bas cat torsion_bas, base_pt, fake_coeffs_new); //run the sieve
      necessary_pr[index][om] := necessary_primes1;
      print "necessary primes",necessary_pr[index][om];
      if d_f then
        done_pr[index][om] := ordinary_primes cat [aux_int];
        done_fake[index][om] := true;
        print d_f, ordinary_primes cat [aux_int];
        break ind;
      end if;
      Left := [fake_coeffs_new[i] : i in [1..#fake_coeffs_new] | bool_list[i] eq true]; //new, store left cosets for aux_int = 1
      if d_f eq false then //if aux_int = 1 does not succeed, try aux_int > 1
        for aux_int in AuxSet do 
          print "Attention aux_int is",aux_int;
          printf "number of cosets: %o\n", #Left; //new
          M := ordinary_M*aux_int;
          fake_coeffs_mod_M := combine_fake_good(Left, ordinary_M, aux_int); //we factor in aux_int > 1
          printf "after aux_int: %o\n", #fake_coeffs_mod_M;
          fake_coeffs_new  := fake_coeffs_mod_M;
          if aux_int eq 2 then //if aux_int = 2, we have pre-computed mws_primes
            mws_primes := MWSPrimes2[index];
          end if;
          if aux_int eq 4 then //if aux_int = 4, we have pre-computed mws_primes
            mws_primes := MWSPrimes4[index];
          end if;  
          if aux_int in [2,4] eq false then //if aux_int is not in [2,4], we have to compute mws_primes
            mws_primes := sieving_primes(M, A, groups, 0.5 : printlevel := 0);
          end if;
          print("mws_primes");
          print mws_primes;
          d_f,necessary_primes2,bool_list := MWSieve(J, mws_primes, M, bas cat torsion_bas, base_pt, fake_coeffs_new);
          if d_f then //if the sieve is successful, we store the ordinary_primes and aux_int we used for each element of Omega
            necessary_pr[index][om] := necessary_primes1 cat necessary_primes2;
            print "necessary primes",necessary_pr[index][om];
            done_pr[index][om] := ordinary_primes cat [aux_int];
            done_fake[index][om] := true;
            print d_f, ordinary_primes cat [aux_int];
            break ind;
            break aux_int;
          end if;
        end for;
      end if;
    end for;
  end for;
  if false in done_fake[index] then 
    Failed := Failed cat [index];
  end if;
  //assert (false in done_fake[index]) eq false;
  print "Failed",Failed;
end for;
assert Failed eq [];
print "Failed",Failed;
