/* This code accompanies the paper ''Weak instances of class group action based cryptography via self-pairings'' */
clear;

//curve setup
p := 179458488738991046657;
Fp := GF(p);
Fpx<x> := PolynomialRing(Fp);

E := EllipticCurve([Fp ! 106960359001385152381, 100704579394236675333]);
t := TraceOfFrobenius(E);
N := p+1-t;
m2 := 2^30;
B := 2^15;
P0 := E ! [97945929612774285314, 157291466096854908830];
tateP0 := ReducedTatePairing(P0,P0,m2);

// small primes ell_i for computation of group action
ells := [5,7,11,13,17,19,23,29,31];
exts := [Order(GF(a) ! p) : a in ells];

// computing all traces of Frobenius over extensions
Traces := [2, t];
for i := 1 to Maximum(exts) do  
   tk1 := (t*Traces[#Traces] - p*Traces[#Traces-1]);
   Append(~Traces, tk1);
end for;

Cards := [p^(k-1) + 1 - Traces[k] : k in [2..#Traces]];

function PointOrderEll(E, ell, e, Ne)  // generates points in eigenspace, either rational or other (non-rational) where e is extension degree
   Fpe := GF(p,e);
   EE := BaseExtend(E, Fpe);
   v := Valuation(Ne, ell);
   Q := Random(EE);
   while true do
     Q := (Ne div ell^v)*Random(EE);
	 if (e gt 1) then Q := (EE ! [Q[1]^p, Q[2]^p]) - Q; end if;  // getting rid of rational part
	 if (Q[3] ne 0) then break; end if;
   end while;
   while ((ell*Q)[3] ne 0) do
	 Q := ell*Q;
   end while;
   return Q;
end function;

// naive implementation of small isogenies
// LR = 0 means walk in the rational direction 
// LR = 1 means walk in the non-rational direction

function DoStep(E, ell, LR)
   e := 1;
   Ne := N;
   if (LR eq 1) then 
     e := exts[Index(ells, ell)];
	 Ne := Cards[e];
   end if;
  Q := PointOrderEll(E, ell, e, Ne); 
  Fpe := Parent(Q[1]);
  Fpey<y> := PolynomialRing(Fpe);
  Ephi, phi := IsogenyFromKernel(E, Fpx ! &*[(y - (k*Q)[1]) : k in [1..ell-1]]);
  return Ephi, phi;
end function;

// pick secret exponents for isogeny of degree 5^2*7*11*13 at random
secret_exps := [Random(1) : i in [1..4]];

// compute corresponding isogeny of degree degr
E1, phi1 := DoStep(E, 5, secret_exps[1]);
E2, phi2 := DoStep(E1, 7, secret_exps[2]);
E3, phi3 := DoStep(E2, 11, secret_exps[3]);
E4, phi4 := DoStep(E3, 13, secret_exps[4]);
E5, phi5 := DoStep(E4, 5, secret_exps[1]); //two steps of degree 5 to reach the maximum degree we can handle (<2^15)
degr := 5^2*7*11*13;

// computing correct image under isogeny
PhiP0 := phi5(phi4(phi3(phi2(phi1(P0)))));
tatePhiP0 := ReducedTatePairing(PhiP0, PhiP0, m2);

// sanity check of pairing values
print "Equality of pairing values sanity check: ", tatePhiP0 eq tateP0^degr;

// deriving the images on E' directly using self-pairing
Ep := E5;
Pp := (N div m2)*Random(Ep);
while Order(Pp) ne m2 do
  Pp := (N div m2)*Random(Ep);
end while;
tatePp := ReducedTatePairing(Pp,Pp,m2);

// computing square-root
Rm2 := Integers(m2);
e := (Rm2 ! Log(tateP0,tatePp))/degr;  
sq, sqr := IsSquare(e);
sqr := Integers() ! sqr;

// sanity check we get one of the correct possibilities
if (m2 mod 2 eq 0) then // we have 4 roots in this case
  R := sqr*PhiP0;
  print "Get one of 4 possibilities: ", R eq Pp or -R eq Pp or ((m2 div 2) - 1)*R eq Pp or ((m2 div 2) + 1)*R eq Pp;
else
  R := sqr*PhiP0;
  print "Get one of 2 possibilities: ", R eq Pp or -R eq Pp;
end if;

// De Feo et al. trick to transform torsion point images of cyclic subgroup to torsion point images of non-cyclic subgroup
function SplitTorsion(E, P, ell, k, N)  // P has order ell^(2*k) and want to push this up and create kernelpoint of upgoing isogeny

  K := ell^k*P;  // kernel point
  Es := [E];
  EIsos := [* *];
  Pm := P;   // image of P under composition of isogenies
  for i := 1 to k do	
    Kp := ell^(k-i)*K;
    Ep, phi := IsogenyFromKernel(Es[i], &*[(x - Fp ! (j*Kp)[1]) : j in [1..ell-1]]);
    Pm := phi(Pm);
	Append(~Es, Ep);
	Append(~EIsos, phi);	
	K := phi(K);
  end for; 
  Etop := Es[k+1];
  
  // want to avoid going to extension fields so finding the kernel by peeling off ell digits
  // constructing independent point of order ell^k
  Qm := Pm;
  while true do
    Qm := (N div ell^(2*k))*Random(Etop);
	if ((ell^(k-1)*Qm)[3] ne 0) then // order equals ell^k
	   if WeilPairing(Pm, Qm, ell^k)^(ell^(k-1)) ne 1 then  // independent
	     break;
	   end if;
	end if;
  end while;
  
  // pushing Qm, Pm through the dual isogeny  (we can end up on an isomorphic curve, otherwise we could have used K)
  Qd := Qm;
  Pd := Pm;
  for i := k to 1 by -1 do
    Qd := DualIsogeny(EIsos[i])(Qd);  
	Pd := DualIsogeny(EIsos[i])(Pd);  
  end for;

  // Pd and Qd are now dependent, so compute dlog
  alpha := Log(Pd, Qd);
  Qm := Qm - alpha*Pm;
 
  // sanity check
  Qd := Qm;
  for i := k to 1 by -1 do
    Qd := DualIsogeny(EIsos[i])(Qd);  
  end for;
  if (Qd[3] ne 0) then 
	  print "Constructed point not in the kernel";
  end if;
  return Etop, Pm, Qm;
end function;

function DefeoTrick(E0, E1, P0, P1, B, A, ell, N)   // P1 = phi(P0), order B^2, degree phi = A, B = l^k
  k := Valuation(B, ell);
  E0top, P0t, Q0t := SplitTorsion(E0, P0, ell, k, N);
  E1top, P1t, Q1t := SplitTorsion(E1, P1, ell, k, N);
  u0 := WeilPairing(P0t, Q0t, ell^k);
  u1 := WeilPairing(P1t, Q1t, ell^k);  
  eu := Log(u0, u1);
  alpha := Integers() ! (A*(Integers(B) ! eu)^-1);
  Q1t := alpha*Q1t;
  return E0top, P0t, Q0t, E1top, P1t, Q1t;
end function;

// apply De Feo et al. trick to our example
E0p, P0p, Q0p, E1p, P1p, Q1p := DefeoTrick(E, E5, P0, PhiP0, B, degr, 2, N);

// check if we recovered the correct torsion point images (taking different order of walk to test)
E0t := E0p;
E1t, phi1t := DoStep(E0t, 5, secret_exps[1]);
E2t, phi2t := DoStep(E1t, 7, secret_exps[2]);
E3t, phi3t := DoStep(E2t, 11, secret_exps[3]);
E4t, phi4t := DoStep(E3t, 5, secret_exps[1]);  
E5t, phi5t := DoStep(E4t, 13, secret_exps[4]); 

// see if we are on the same curve
bIso, MapIso := IsIsomorphic(E1p, E5t);  // computing explicit isomorphism if needed

// check correctness of torsion point information 
print "Check on image of P", P1p eq phi5t(phi4t(phi3t(phi2t(phi1t(P0p)))));
print "Check on image of Q", MapIso(Q1p) eq phi5t(phi4t(phi3t(phi2t(phi1t(Q0p)))));