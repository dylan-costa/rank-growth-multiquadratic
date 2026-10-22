///////////////////////////////////////////////////////////////////////////
//
//  EllipticRankTwists.m
//
//  Magma code for D. T. Costa and A. Lozano-Robledo, "Elliptic curve rank
//  growth in multi-quadratic extensions" (Section 6 of the paper).
//  Result numbers below refer to the paper.
//
//  Two functions:
//
//    (1) NaiveRootNumberTwistSearch(E, N : keep := 1)
//        Brute-force search over the integers x in [-N..N] for quadratic
//        twists E^{f(x)} whose root number is +1 (so that, under the Parity
//        Conjecture 4.3, the twist has even rank, hence rank >= 2 when the
//        point coming from x has infinite order). After the whole range is
//        scanned, returns the "keep" twists d of smallest |d| (keep = 1 by
//        default).
//
//    (2) ConstructRootNumberTwists(E, epsilon : howmany, W, BadPrimes, tries)
//        The factoring-free construction of Remark 5.7 (Lemma 5.4, Lemma 5.5,
//        Theorem 5.6): square-free d_1, ..., d_howmany with
//        W(E^{d_k}) = epsilon (+1 or -1), a point of infinite order on each
//        E^{d_k}, and Q(sqrt d_1, ..., sqrt d_n) of degree 2^n. W(E) and the
//        bad primes are optional: pass them for curves of enormous
//        conductor, where Conductor and RootNumber are too slow.
//
//  Neither function computes ranks or class groups, and loading this file
//  changes no global Magma settings.
//
///////////////////////////////////////////////////////////////////////////


function SquarefreePart(q)
    if q eq 0 then
        return 0;
    end if;
    n := Numerator(q);
    d := Denominator(q);      // always > 0 in Magma's normal form
    m := n*d;
    s := Sign(m);
    m := Abs(m);
    fac := Factorization(m);
    sf := 1;
    for pe in fac do
        if IsOdd(pe[2]) then
            sf *:= pe[1];
        end if;
    end for;
    return s*sf;
end function;


///////////////////////////////////////////////////////////////////////////
// (1) NAIVE SEARCH
///////////////////////////////////////////////////////////////////////////
//
// Input:
//   E               : elliptic curve over Q with integral a-invariants.
//                      Its short model WeierstrassModel(E) is
//                      y^2 = f(x) = x^3 + A*x + B with A, B integers.
//   N               : a non-negative integer. Every integer x in [-N..N]
//                      is tried, so each f(x) is an integer.
//   KnownConductor  : (optional) the conductor of E, if already known
//                      (e.g. from a database) -- saves recomputing it.
//                      0 (default) means "compute it via Conductor(E)".
//   KnownRootNumber : (optional) the root number of E, if already known.
//                      0 (default) means "compute it via RootNumber(E)".
//   keep            : (optional) how many twists to return. Default 1,
//                      i.e. only the twist of least |d| found in xrange.
//
// Output:
//   BestTwists : a sequence of (at most) keep square-free integers d, the
//                ones of smallest |d| among all d found for x in [-N..N]
//                such that the discriminant D of Q(sqrt d) (D = d if
//                d = 1 mod 4, else 4d) is prime to N_E, and the quadratic
//                twist E^d (equivalently, the twist of E by f(x) for the
//                corresponding x) has root number +1. Other d are never
//                returned: Lemma 4.6 and Lemma 5.2
//                need gcd(D, N_E) = 1.
//                Sorted by |d| increasing; when d and -d both
//                occur, -d comes first. Fewer than keep are returned if
//                fewer were found, and [] if none were.
//   AllTwists  : (second return value) every such d found, sorted the
//                same way.
//
//
///////////////////////////////////////////////////////////////////////////

function NaiveRootNumberTwistSearch(E, N : KnownConductor := 0, KnownRootNumber := 0, keep := 1)

    error if Type(N) ne RngIntElt or N lt 0,
        "NaiveRootNumberTwistSearch: N must be a non-negative integer; x runs over [-N..N]";
    error if Type(keep) ne RngIntElt or keep lt 1, "NaiveRootNumberTwistSearch: keep must be a positive integer";

    Eshort := WeierstrassModel(E);
    ai := aInvariants(Eshort);
    A := Integers()!ai[4];
    B := Integers()!ai[5];

    NE := (KnownConductor eq 0)  select Conductor(Eshort)  else KnownConductor;
    W  := (KnownRootNumber eq 0) select RootNumber(Eshort) else KnownRootNumber;
    NEodd := IsOdd(NE);

    RankTwoCandidates := {};

    for x := -N to N do

        fx := x^3 + A*x + B;
        if fx eq 0 or IsSquare(fx) then
            continue;   // fx=0, or trivial twist (d=1) -- cheap checks, no factoring
        end if;

        g := Gcd(fx, NE);

        if g eq 1 and (NEodd or ((fx mod 4) eq 1)) then
            // fast path: no factorization needed at all (see note above)
            w := KroneckerSymbol(fx, -NE) * W;
            d := 0;   // not yet computed -- only if this turns out to be a hit
        else
            // slow path (rare: shares a factor with N_E, or N_E even and
            // fx = 3 mod 4): need the actual square-free part
            d := SquarefreePart(fx);
            // Only twists whose discriminant D (d or 4d) is prime to N_E. The fast
            // path already has this: gcd(fx, NE) = 1, and fx = d = 1 mod 4 if NE is even.
            if Gcd((d mod 4 eq 1) select d else 4*d, NE) ne 1 then
                continue;
            end if;
            Ed := QuadraticTwist(Eshort, d);
            w := RootNumber(Ed);
        end if;

        if w eq 1 then
            if d eq 0 then
                d := SquarefreePart(fx);   // only paid for actual hits
            end if;
            Include(~RankTwoCandidates, d);
        end if;

    end for;

    // Order by |d| (ties: -d before d) and keep the best "keep" of them.
    AllTwists := Sort(SetToSequence(RankTwoCandidates),
                      func< a, b | Abs(a) ne Abs(b) select Abs(a) - Abs(b) else a - b >);
    BestTwists := AllTwists[1..Min(keep, #AllTwists)];

    return BestTwists, AllTwists;

end function;


///////////////////////////////////////////////////////////////////////////
// (2) CONSTRUCTIVE METHOD
///////////////////////////////////////////////////////////////////////////
//
//
// tries = m > howmany constructs k = 1, ..., m and returns the howmany of
// least |d_k|. Any subset of the d_k keeps all the properties above.
//
// Input:
//   E            : elliptic curve over Q with integral a-invariants
//   epsilon      : the root number wanted for every twist, 1 or -1
//   howmany      : (optional, default 1) number of twists
//   W            : (optional) W(E), 1 or -1. Default 0: RootNumber(E)
//   BadPrimes    : (optional) set or sequence of the primes dividing N_E.
//                  Default {}: PrimeDivisors(Conductor(E)), far too slow for
//                  the record curves. When given, it is checked that no prime
//                  of Disc(E) is missing (a missing prime would give the wrong
//                  root number); an extra prime is harmless.
//   tries        : (optional) see above. Default 0: m = howmany
//   FactorDigits : (optional, default 50) see Cost
//
// Output:
//   ds   : [d_1, ..., d_howmany], in the order k = 1, 2, ... (by |d| if tries
//          was used)
//   recs : list of records, in the same order, with fields
//     k       : the step that produced it
//     d       : d_k (see dProven)
//     dProven : true if d_k came from a complete factorization
//     z       : z_k
//     fz      : f(z_k)
//     K       : Q(sqrt(d_k))
//     P       : the point (fz*z, fz^2) of infinite order on
//               Y^2 = X^3 + A*fz^2*X + B*fz^3, a model of E^{d_k}
//     q, Q    : q_k and Q_k = q_1 ... q_k, so z_k = x_1 / (Q*N)^2
//     x10, M  : x_1 = x10 mod M, x10 the least non-negative representative
//
///////////////////////////////////////////////////////////////////////////

// Square-free part of a nonzero integer, with bounded factoring effort:
// trial division up to 10^6, then a full Factorization of the cofactor only
// if it has at most `digits` digits. Returns d and whether it is proven.
function SquarefreePartLimited(n, digits)
    // Not TrialDivision: in Magma 2.25 it never returns on some inputs
    // (a 1118-digit f(z_6) of ICARM curve 398), and this loop is also faster.
    c := Abs(n);
    fac := [car< Integers(), Integers() > | ];
    for p in PrimesUpTo(10^6) do
        if c mod p eq 0 then
            e := 0;
            repeat c div:= p; e +:= 1; until c mod p ne 0;
            Append(~fac, <p, e>);
        end if;
    end for;
    proven := true;
    if c ne 1 and #IntegerToString(c) le digits then
        for pe in Factorization(c) do Append(~fac, <pe[1], pe[2]>); end for;
        c := 1;
    end if;
    d := Sign(n);
    for pe in fac do
        if IsOdd(pe[2]) then d *:= pe[1]; end if;
    end for;
    if c ne 1 then
        if IsSquare(c) then
            // square cofactor: contributes nothing, d is still exact
        elif IsProbablePrime(c) then
            d *:= c;
        else
            d *:= c;            // unfactored composite, assumed square-free
            proven := false;
        end if;
    end if;
    return d, proven;
end function;

function ConstructRootNumberTwists(E, epsilon : howmany := 1, W := 0, BadPrimes := {},
                                   tries := 0, FactorDigits := 50)

    error if epsilon notin {1, -1}, "ConstructRootNumberTwists: epsilon must be 1 or -1";
    error if Type(howmany) ne RngIntElt or howmany lt 1,
        "ConstructRootNumberTwists: howmany must be a positive integer";
    m := tries eq 0 select howmany else tries;
    error if Type(m) ne RngIntElt or m lt howmany,
        "ConstructRootNumberTwists: tries must be 0 or an integer >= howmany";
    error if W notin {0, 1, -1}, "ConstructRootNumberTwists: W must be 1 or -1 (0 = compute it)";

    if #BadPrimes eq 0 then
        BadPrimes := PrimeDivisors(Conductor(E));
    else
        BadPrimes := SetToSequence(Set(BadPrimes));
        error if exists{p : p in BadPrimes | not IsProbablePrime(p)},
            "ConstructRootNumberTwists: every element of BadPrimes must be prime";
        left := Integers()!Discriminant(E);
        for p in BadPrimes do
            while left mod p eq 0 do left div:= p; end while;
        end for;
        // What is left can only come from primes where the model is not minimal.
        left := Abs(left);
        error if left ne 1 and (#IntegerToString(left) gt 60 or
                 exists{p : p in PrimeDivisors(left) | LocalInformation(E, p)[3] gt 0}),
            "ConstructRootNumberTwists: BadPrimes misses a prime dividing the conductor";
    end if;
    if W eq 0 then
        W := RootNumber(E);
    end if;
    sgn := epsilon * W;   // sign(d_k), so that W(E^{d_k}) = sign(d_k) W(E) = epsilon

    ai := aInvariants(WeierstrassModel(E));
    A := Integers()!ai[4];
    B := Integers()!ai[5];
    Tthr := Abs(A) + Abs(B) + 1;

    Nprimes    := Sort(SetToSequence(Set(BadPrimes) join {2, 3, 5, 7}));
    oddPrimesN := [p : p in Nprimes | p ne 2];
    N          := &*Nprimes;

    RF := recformat< k, d, dProven, z, fz, K, P, q, Q, x10, M >;
    results := [* *];

    auxPrimes := [];   // q_1, ..., q_k
    q := 2;

    for k in [1..m] do

        repeat
            q := NextPrime(q);
        until N mod q ne 0;
        Append(~auxPrimes, q);
        Q := &*auxPrimes;

        t := 2;
        while LegendreSymbol(t, q) ne -1 do
            t +:= 1;
        end while;

        // x_1 = 1 mod 8, mod each odd p | N and mod q_1..q_{k-1}; t mod q_k.
        moduli   := [8] cat oddPrimesN cat auxPrimes;
        residues := [1 : i in [1..#moduli - 1]] cat [t];
        M   := &*moduli;
        x10 := CRT(residues, moduli);

        QN2   := (Q*N)^2;
        bound := Tthr * QN2;
        x1 := sgn eq 1 select x10 + M*Ceiling((bound - x10)/M)
                        else  x10 - M*Ceiling((bound + x10)/M);
        z  := x1 / QN2;
        fz := z^3 + A*z + B;

        // Explicit coefficients rather than QuadraticTwist, which may try to minimize.
        Ed := EllipticCurve([0,0,0, A*fz^2, B*fz^3]);
        P  := Ed ! [fz*z, fz^2, 1];   // image of (z, 1) on fz*y^2 = f(x)

        d, dProven := SquarefreePartLimited(Numerator(fz), FactorDigits);
        K  := NumberField(Polynomial([-(dProven select d else fz), 0, 1]));

        Append(~results, rec< RF | k := k, d := d, dProven := dProven,
                                    z := z, fz := fz, K := K, P := P,
                                    q := q, Q := Q, x10 := x10, M := M >);

    end for;

    if m gt howmany then
        // Keep the howmany of least |d| (ties: -d first).
        idx := Sort([1..m], func< i, j | Abs(results[i]`d) ne Abs(results[j]`d)
                                         select Abs(results[i]`d) - Abs(results[j]`d)
                                         else results[i]`d - results[j]`d >);
        results := [* results[i] : i in idx[1..howmany] *];
    end if;
    return [r`d : r in results], results;

end function;

