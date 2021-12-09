#include <stdio.h>
#include <stdlib.h>
#include <pari/pari.h>
#include <pari/paripriv.h>
#include <math.h>
#include "twistminimal.h"
#include <sys/file.h>


typedef struct
{
    long p;
    long e;
    long s;
    long psi2s;
    GEN values;
    GEN barValues;
    GEN order;
} TwistAtPrime;

typedef struct
{
    long numP;
    TwistAtPrime chiPs[6];
} TwistFactors;

typedef struct
{
    TwistFactors chiPfactors;
    GEN gcds;
    long M;
    long Mdash;
} TwistChar;


/* fa = factorization of -D > 0, return -D0 > 0 (where D0 is fundamental) */
static long
corediscs_fact(GEN fa)
{
    GEN P = gel(fa,1), E = gel(fa,2);
    long i, l = lg(P), m = 1;
    for (i = 1; i < l; i++)
    {
        long p = P[i], e = E[i];
        if (e & 1) m *= p;
    }
    if ((m&3L) != 3) m <<= 2;
    return m;
}

enum { cache_FACT, cache_DIV, cache_H, cache_D, cache_DIH };
typedef struct
{
    const char *name;
    GEN cache;
    ulong minself, maxself;
    void (*init)(long);
    ulong miss, maxmiss;
    long compressed;
} cache;

static void constfact(long lim);
static void constdiv(long lim);
static void consttabh(long lim);
static void constcoredisc(long lim);
static THREAD cache caches[] =
{
    { "Factors",  NULL,  50000,    50000, &constfact, 0, 0, 0 },
    { "Divisors", NULL,  50000,    50000, &constdiv, 0, 0, 0 },
    { "H",        NULL, 100000, 10000000, &consttabh, 0, 0, 1 },
    { "CorediscF",NULL, 100000, 10000000, &constcoredisc, 0, 0, 0 },
};

static void
cache_reset(long id)
{
    caches[id].miss = caches[id].maxmiss = 0;
}
static void
cache_set(long id, GEN S)
{
    GEN old = caches[id].cache;
    caches[id].cache = gclone(S);
    guncloneNULL(old);
}

static GEN
cache_get(long id, ulong D)
{
    cache *S = &caches[id];
    const ulong d = S->compressed? D>>1: D;
    ulong max, l;

    if (!S->cache)
    {
        max = maxuu(minuu(D, S->maxself), S->minself);
        S->init(max);
        l = lg(S->cache);
    }
    else
    {
        l = lg(S->cache);
        if (l <= d)
        {
            if (D > S->maxmiss) S->maxmiss = D;
            if (DEBUGLEVEL >= 3)
                err_printf("miss in cache %s: %lu, max = %lu\n",
                           S->name, D, S->maxmiss);
            if (S->miss++ >= 5 && D < S->maxself)
            {
                max = minuu(S->maxself, (long)(S->maxmiss * 1.2));
                if (max <= S->maxself)
                {
                    if (DEBUGLEVEL >= 3)
                        err_printf("resetting cache %s to %lu\n", S->name, max);
                    S->init(max);
                    l = lg(S->cache);
                }
            }
        }
    }
    return (l <= d)? NULL: gel(S->cache, d);
}

static GEN
update_factor_cache(long a, long lim, long *pb)
{
    const long step = 16000; /* even; don't increase this: RAM cache thrashing */
    if (a + 2*step > lim)
        *pb = lim; /* fuse last 2 chunks */
    else
        *pb = a + step;
    return vecfactoroddu_i(a, *pb);
}

/* assume lim < MAX_LONG/8 */
static void
constcoredisc(long lim)
{
    pari_sp av2, av = avma;
    GEN D = caches[cache_D].cache, CACHE = NULL;
    long cachea, cacheb, N, LIM = !D ? 4 : lg(D)-1;
    if (lim <= 0) lim = 5;
    if (lim <= LIM) return;
    cache_reset(cache_D);
    D = zero_zv(lim);
    av2 = avma;
    cachea = cacheb = 0;
    for (N = 1; N <= lim; N+=2)
    {
        /* N odd */
        long i, d, d2;
        GEN F;
        if (N > cacheb)
        {
            set_avma(av2);
            cachea = N;
            CACHE = update_factor_cache(N, lim, &cacheb);
        }
        F = gel(CACHE, ((N-cachea)>>1)+1); /* factoru(N) */
        D[N] = d = corediscs_fact(F); /* = 3 mod 4 or 4 mod 16 */
        d2 = odd(d)? d<<3: d<<1;
        for (i = 1;;)
        {
            if ((N << i) > lim) break;
            D[N<<i] = d2;
            i++;
            if ((N << i) > lim) break;
            D[N<<i] = d;
            i++;
        }
    }
    cache_set(cache_D, D);
    set_avma(av);
}

static
GEN addPowersToFactors(GEN factors)
{
    GEN fullVersion = gcopy(factors);
    GEN fullFactor, factor, P, E;
    for (long j = 1; j<lg(factors); j++)
    {
        factor = gel(factors,j);
        P = gel(factor,1);
        E = gel(factor,2);
        fullFactor = mkvec3(gcopy(P),gcopy(E),gcopy(E));
        for (long i = 1; i<lg(P); i++)
        {
            gel(fullFactor,3)[i]= upowuu(P[i],E[i]);
        }
        gel(fullVersion, j) = gcopy(fullFactor);
    }
    return fullVersion;
}

static void
constfact(long lim)
{
    pari_sp av;
    GEN VFACT = caches[cache_FACT].cache;
    long LIM = VFACT? lg(VFACT)-1: 4;
    if (lim <= 0) lim = 5;
    if (lim <= LIM) return;
    cache_reset(cache_FACT);
    av = avma;
    GEN factors = vecfactoru_i(1, lim);
    factors = addPowersToFactors(factors);
    cache_set(cache_FACT, factors);
    set_avma(av);
}
static void
constdiv(long lim)
{
    pari_sp av;
    GEN VFACT, VDIV = caches[cache_DIV].cache;
    long N, LIM = VDIV? lg(VDIV)-1: 4;
    if (lim <= 0) lim = 5;
    if (lim <= LIM) return;
    constfact(lim);
    VFACT = caches[cache_FACT].cache;
    cache_reset(cache_DIV);
    av = avma;
    VDIV  = cgetg(lim+1, t_VEC);
    for (N = 1; N <= lim; N++) gel(VDIV,N) = divisorsu_fact(gel(VFACT,N));
    cache_set(cache_DIV, VDIV);
    set_avma(av);
}
/* n > 1, D = divisors(n); sets L = 2*lambda(n), S = sigma(n) */
static void
lamsig(GEN D, long *pL, long *pS)
{
    pari_sp av = avma;
    long i, l = lg(D), L = 1, S = D[l-1]+1;
    for (i = 2; i < l; i++) /* skip d = 1 */
    {
        long d = D[i], nd = D[l-i]; /* nd = n/d */
        if (d < nd)
        {
            L += d;
            S += d + nd;
        }
        else
        {
            L <<= 1;
            if (d == nd)
            {
                L += d;
                S += d;
            }
            break;
        }
    }
    set_avma(av);
    *pL = L;
    *pS = S;
}
static void
consttabh(long lim)
{
    pari_sp av = avma, av2;
    GEN VHDH0, VDIV, CACHE = NULL;
    GEN VHDH = caches[cache_H].cache;
    long r, N, cachea, cacheb, lim0 = VHDH? lg(VHDH)-1: 2, LIM = lim0 << 1;

    if (lim <= 0) lim = 5;
    if (lim <= LIM) return;
    cache_reset(cache_H);
    r = lim&3L;
    if (r) lim += 4-r;
    cache_get(cache_DIV, lim);
    VDIV = caches[cache_DIV].cache;
    VHDH0 = cgetg(lim/2 + 1, t_VECSMALL);
    VHDH0[1] = 2;
    VHDH0[2] = 3;
    for (N = 3; N <= lim0; N++) VHDH0[N] = VHDH[N];
    av2 = avma;
    cachea = cacheb = 0;
    for (N = LIM + 3; N <= lim; N += 4)
    {
        long s = 0, limt = usqrt(N>>2), flsq = 0, ind, t, L, S;
        GEN DN, DN2;
        if (N + 2 >= lg(VDIV))
        {
            /* use local cache */
            GEN F;
            if (N + 2 > cacheb)
            {
                set_avma(av2);
                cachea = N;
                CACHE = update_factor_cache(N, lim+2, &cacheb);
            }
            F = gel(CACHE, ((N-cachea)>>1)+1); /* factoru(N) */
            DN = divisorsu_fact(F);
            F = gel(CACHE, ((N-cachea)>>1)+2); /* factoru(N+2) */
            DN2 = divisorsu_fact(F);
        }
        else
        {
            /* use global cache */
            DN = gel(VDIV,N);
            DN2 = gel(VDIV,N+2);
        }
        ind = N >> 1;
        for (t = 1; t <= limt; t++)
        {
            ind -= (t<<2)-2; /* N/2 - 2t^2 */
            if (ind) s += VHDH0[ind];
            else flsq = 1;
        }
        lamsig(DN, &L,&S);
        VHDH0[N >> 1] = 2*S - 3*L - 2*s + flsq;
        s = 0;
        flsq = 0;
        limt = (usqrt(N+2) - 1) >> 1;
        ind = (N+1) >> 1;
        for (t = 1; t <= limt; t++)
        {
            ind -= t<<2; /* (N+1)/2 - 2t(t+1) */
            if (ind) s += VHDH0[ind];
            else flsq = 1;
        }
        lamsig(DN2, &L,&S);
        VHDH0[(N+1) >> 1] = S - 3*(L >> 1) - s - flsq;
    }
    cache_set(cache_H, VHDH0);
    set_avma(av);
}

/*Return conductor of character*/
long
vchip_FC(GEN VCHI)
{
    return lg(gel(VCHI,1))-1;
}

/*Return gcd of N and x where GCD is an array of known GCDs for N*/
static long
myugcd(GEN GCD, ulong x)
{
    ulong N = lg(GCD)-1;
    if (x >= N) x %= N;
    return GCD[x+1];
}

//Get factor of N from cache
GEN
myfactoru(long N)
{
    GEN z = cache_get(cache_FACT, N);
    return z? gcopy(z): factoru(N);
}

/* getCharGroup for p^e*/
GEN
getCharGroup(long p, long e)
{
    return znstar0(powuu(p, e),0);
}

/*Takes in group and a variable number and returns a vector of
the variable along with a cyclotomic polynomial order size of group*/
GEN
getMaximalChipMod(GEN group, long variableNumber)
{
    //This is kind of the cyclotomic polynomial, but we don't simplify it as that would result in
    //some values being incorrect. For example, an order 6 character might have a value -1 where
    //the order 3 embedding has value 1. We want the order 6 character to say x^3 even though this
    //can be simplified, so that later we can take mod x^6-1 when embedding (x^2)^3
    GEN pol = gdiv(gsub(pol_xn(itos(gel(group,1)), variableNumber+1),gen_1),gsub(pol_x(variableNumber+1),gen_1));
    //pol_x gives us the variable as a monomial
    return mkvec3(group,pol_x(variableNumber+1), pol);
}

/*Given a character for weight 2, return arrays of values for each 2Re(chi_p(x)) as
this is how it is always evaluated*/
static GEN
getTwistCharValues(long p, GEN chip)
{
    GEN group = gel(chip,1);
    if (gequal1(gel(group,1)))
    {
        return mkvec(gen_1);
    }
    GEN entry = gel(chip,2);
    //The level and generator of the character
    long level = itos(gel(gel(gel(group,3),1),1));
    long generator = itos(gel(gel(gel(group,3),1),2));
    //Every value is 0 unless reached by the generator
    GEN chipValues = zerovec(level);
    //Multiplying the generator by itself each time
    for (long j=generator; j!=1; j=j*generator%level)
    {
        //The value is taken mod the cyclotomic polynomial
        gel(chipValues,j) = gadd(entry, RgXQ_inv(entry, gel(chip,3)));
        //Then the entry is multiplied by the variable monomial
        entry = RgXQ_mul(entry, gel(chip,2), gel(chip,3));
    }
    //Finally, the value at 1 is set to 2 (real part of chi(1) is 1)
    gel(chipValues,1) = gen_2;
    return chipValues;
}

/**/
GEN
getQuadraticValues(long p, GEN chip)
{
    //Garbage collection on chi_p, group and entry
    pari_sp ltop = avma;
    GEN group = gel(chip,1);
    GEN entry = gen_m1;
    pari_sp lbottom = avma;
    //The level and generator of the character
    long level = p;
    long generator = itos(gel(gel(gel(group,3),1),2));
    //Every value is 0 unless reached by the generator
    GEN chipValues = zerovec(level);
    //Multiplying the generator by itself each time
    for (long j=generator; j!=1; j=j*generator%level)
    {
        //The value is taken mod the cyclotomic polynomial
        gel(chipValues,j) = entry;
        //Then the entry is multiplied by the variable monomial
        entry = gmul(entry,gen_m1);
    }
    //Finally, the value at 1 is set to 1
    gel(chipValues,1) = gen_1;
    return gerepile(ltop, lbottom,chipValues);
}

/* Given an array of values for a character, return the
evaluation of that character at x */
static GEN
evaluateCharValues(GEN chiValues, long x)
{
    //N is the level of the character
    long N = lg(chiValues)-1;
    //Take x mod N, between 1 and N
    x = umodsu(x-1,N)+1;
    //Return chi(x)
    return gel(chiValues, x);
}

//Given precomputed conj(x) mod some N up to N, return conj(n).
static long getNBar(GEN nbars, long n)
{
    //N is the modulus
    long N = lg(nbars)-1;
    //Return nbar
    return nbars[umodsu(n,N)];
}

//Given a vector of sorted ints, return the position of a target int, or -1 if it doesn't feature
static int
binarySearch(GEN vector, long lower, long upper, long target)
{
    if (upper==lower) return vector[lower]==target? lower: -1;
    long lookat = (lower+upper)/2;
    if (vector[lookat]==target) return lookat;
    if (vector[lookat]<target) return binarySearch(vector, lookat+1, upper, target);
    return lower==lookat? -1: binarySearch(vector, lower, lookat-1, target);
}

//Get the exponent of a given p in a factorisation
static long
getexponent(GEN faCHIP, long p)
{
    pari_sp av = avma;
    GEN P = gel(faCHIP, 1);
    GEN E = gel(faCHIP, 2);
    if (lg(P)==1) return gc_long(av, 0);
    long pos = binarySearch(P, 1, lg(P)-1, p);
    if (pos==-1) return gc_long(av, 0);
    return gc_long(av, E[pos]);
}

//As above, but returning p^e in a factorisation
static long
getpower(GEN faCHIP, long p)
{
    pari_sp av = avma;
    GEN P = gel(faCHIP, 1);
    if (lg(P)==1) return gc_long(av, 1);
    long pos = binarySearch(P, 1, lg(P)-1, p);
    if (pos==-1) return gc_long(av, 1);
    return gc_long(av, gel(faCHIP,3)[pos]);
}

//Creates a vector of GCDs for an integer N
GEN
mkgcd(long N)
{
    GEN GCD, d;
    long i, N2;
    if (N == 1) return mkvecsmall(N);
    GCD = cgetg(N + 1, t_VECSMALL);
    d = GCD+1; /* GCD[i+1] = d[i] = gcd(i,N) = gcd(N-i,N), i = 0..N-1 */
    d[0] = N;
    d[1] = d[N-1] = 1;
    N2 = N>>1;
    for (i = 2; i <= N2; i++) d[i] = d[N-i] = ugcd(N, i);
    return GCD;
}

/* write n = dl^2. Return d, set pointer to l. */
static ulong
mycore(ulong n, long *pl)
{
    pari_sp av = avma;
    GEN fa = myfactoru(n), P = gel(fa,1), E = gel(fa,2);
    long i, l = lg(P), m = 1, f = 1;
    for (i = 1; i < l; i++)
    {
        long j, p = P[i], e = E[i];
        if (e & 1) m *= p;
        for (j = 2; j <= e; j+=2) f *= p;
    }
    *pl = f;
    return gc_long(av,m);
}

/* write -n = Dl^2, D < 0 fundamental discriminant. Return D, set l. */
static long
coredisc2neg(ulong n, long *pl)
{
    ulong m, D = (ulong)cache_get(cache_D, n);
    if (D)
    {
        *pl = usqrt(n/D);
        return -(long)D;
    }
    m = mycore(n, pl);
    if ((m&3) != 3)
    {
        m <<= 2;
        *pl >>= 1;
    }
    return (long)-m;
}

/* D < -4 fundamental, h(D), ordinary class number */
static long
myh(long D)
{
    ulong z = (ulong)cache_get(cache_H, -D);
    if (z) return z/6;
    return itou(quadclassno(stoi(D)));
}

//Evaluation of Sp(1,1) from trace formula. Takes in Mdash (level being twisted from)
//L and d such that t^2-4n=dL^2, and faL the factorisation of L.
static GEN
SP11(long Mdash, GEN faL, long L, long d)
{
    pari_sp ltop = avma;
    GEN Pn = gel(faL, 1), En = gel(faL, 2), PnEn = gel(faL, 3);
    long l = lg(Pn), i;
    GEN s = gen_1;
    for (i=1; i<l; i++)
    {
        if (!umodsu(Mdash,Pn[i])) continue;
        switch (kross(d, Pn[i]))
        {
        case 1:
            s = gmulgs(s,PnEn[i]);
            break;
        case 0:
            if (En[i]>1)
            {
                s = gmulgs(s,PnEn[i] + (PnEn[i]-1)/(Pn[i]-1));
            }
            else
            {
                s = gmulgs(s, 1 + PnEn[i]);
            }
            break;
        default:
            if (En[i]>1)
            {
                s = gmulgs(s, PnEn[i] + 2*(PnEn[i]-1)/(Pn[i]-1));
            }
            else
            {
                s = gmulgs(s, 2 + PnEn[i]);
            }
            break;
        }
    }
    return gerepileupto(ltop, s);
}

//given a vecsmall of square roots mod N, and a long x, returns the square root of x mod N
static long
getSQRT(GEN SQRTS, long x)
{
    return SQRTS[umodsu(x,lg(SQRTS)-1)+1];
}

//Creates a vecsmall of square roots for all p^e in factorisation of N
static GEN
mksqr(long N)
{
    if (N==1) return gen_0;
    GEN faN = myfactoru(N);
    GEN PN = gel(faN, 1);
    GEN SQRTS = cgetg(lg(PN),t_VEC);
    //The inner limits are the numbers we have to square for each sqrt vector
    GEN innerlimits = mkvecsmalln(lg(SQRTS)-1);
    //The outer limits are simply the powers
    GEN outerlimits = mkvecsmalln(lg(SQRTS)-1);
    for (long i = 1; i<lg(innerlimits); i++)
    {
        outerlimits[i] = getpower(faN, PN[i]);
        innerlimits[i] = 1+(outerlimits[i]>>1);
        gel(SQRTS,i) = const_vecsmall(outerlimits[i], -1);
    }
    //For even N we take square roots mod 4N
    if (!odd(N))
    {
        innerlimits[1] = outerlimits[1];
        outerlimits[1] <<= 2;
        gel(SQRTS,1) = const_vecsmall(outerlimits[1], -1);
    }
    //Start from 0 and work up to the biggest of the innerlimits
    long x2=0;
    long biggestLimit = vecsmall_max(innerlimits);
    for (long x = 0 ; x < biggestLimit; x++)
    {
        for (long i = 1; i<lg(SQRTS); i++)
        {
            //If we're within the inner limit for given p, add the square root
            if (x<innerlimits[i])
            {
                gel(SQRTS,i)[(x2%outerlimits[i])+1] = x;
            }
        }
        //Move to the next square
        x2 += (x << 1) + 1;
    }
    return SQRTS;
}

//Given a lower level Mdash, n, and twist character psi, return the value of C1 from the formula
static GEN
wt2trivialC1(long Mdash, TwistChar psi, long n)
{
    if (!uissquare(n)) return gen_0;
    GEN S = stoi(Mdash);
    //Evaluate at each factor in turn
    for (long i = 0; i<psi.chiPfactors.numP; i++)
    {
        TwistAtPrime chiP = psi.chiPfactors.chiPs[i];
        long e = chiP.e;
        if (!e) continue;
        long p = chiP.p;
        if (chiP.psi2s == e)   //First case
        {
            S = gadd(S, gdivgs(S,p));
        }
        else //Second case
        {
            switch(e)
            {
            case 1:
                S = gsub(S, gdivgs(S, p));
                break;
            case 2:
                S = gadd(S, gmul(S, gdivgs(gaddsg(-2,gdivsg(1,stoi(p))), p)));
                if (p>2) S = gmul2n(S, -1);
                break;
            default:
                S = gadd(S, gmul(S,gdivgs(gsub(gdivgs(gsub(gdivgs(gen_1,p),gen_1),p),gen_1),p)));
                if (!odd(e) && p>2) S = gmul2n(S, -1);
                break;
            }
        }
    }
    S = gdivgs(S, 12);
    return S;
}

//Evaluate Spmin(p^e,\psi_p) from the trace formula
static GEN
wt2trivialSpMin(GEN factorsN, TwistChar psi, GEN factorsD, GEN factorsL, long n, long L, long d, GEN SQRTS, long t)
{
    //P are primes in factorisation of N, and E are associated exponents
    long twonupl, u, part, ntimes2=n<<1;
    GEN S = gen_1;
    long i = 0, gam, p, e, s, ptothes;

    for (long j = 0; j<psi.chiPfactors.numP; j++)
    {
        if(psi.chiPfactors.chiPs[j].psi2s == psi.chiPfactors.chiPs[j].e && getexponent(factorsD, psi.chiPfactors.chiPs[j].p)<(psi.chiPfactors.chiPs[j].e<<1)-1)
        {
            if (getSQRT(gel(SQRTS,j+1), d)<1) return gen_0;
        }
        else if(psi.chiPfactors.chiPs[j].p != 2 && psi.chiPfactors.chiPs[j].psi2s == 0 && psi.chiPfactors.chiPs[j].e)
        {
            if (getSQRT(gel(SQRTS,j+1), d)>0) return gen_0;
            if (psi.chiPfactors.chiPs[j].e>2 && getexponent(factorsD, psi.chiPfactors.chiPs[j].p)<psi.chiPfactors.chiPs[j].e-2) return gen_0;
        }
    }

    if(psi.chiPfactors.chiPs[0].p==2 && !psi.chiPfactors.chiPs[0].s && getSQRT(gel(SQRTS,1), d)>0) return gen_0;

    //Compute the S_2 factor first
    if (psi.chiPfactors.chiPs[0].p == 2)
    {
        TwistAtPrime chi2 = psi.chiPfactors.chiPs[0];
        s = chi2.s;
        e = chi2.e;
        gam = getexponent(factorsD, 2);
        ptothes = lg(chi2.values)-1;
        if (e)
        {
            if (!s)
            {
                long part = odd(d)? 2: 1;

                if (e< 3)
                {
                    if (e==2 && gam==0) S = gshift(stoi(part),-1);
                    else
                    {
                        S = stoi(-part);
                    }
                }
                else if(gam<e-1)
                {
                    return gen_0;
                }
                else
                {
                    if (e>3) part <<= e-3;
                    if (gam>e || odd(d))part*=-3;
                    S = stoi(part);
                }
            }
            else if (chi2.psi2s == e) //First two cases
            {
                if (gam >= (e<<1))
                {
                    switch (umodsu(d,8))
                    {
                    case 3:
                    case 5:
                        part = 6 * getpower(factorsL, 2) - (3 << e);
                        break;
                    case 0:
                    case 2:
                    case 4:
                    case 6:
                        part = (2 << gam/2) - (3 << (e-1));
                        break;
                    default:
                        part = getpower(factorsL,2) << 1;
                    }
                    if (gam == (e<<1)) S = stoi(-part);
                    else S = stoi(part);
                }
                else if (gam + 1 != (e<<1))
                {
                    u = getSQRT(gel(SQRTS,1), d);
                    u*=L;
                    S = stoi(getpower(factorsL,2));
                    if (!t)
                    {
                        //(chi(-1)+conj(chi(-1)))/2 == chi(-1)
                        S = gmul(S, evaluateCharValues(chi2.values, umodsu(-1,ptothes)));
                    }
                    else
                    {
                        long argument = umodsu(t*(t+u)*getNBar(chi2.barValues,n)/2-1,ptothes);
                        S = gmul(S,evaluateCharValues(chi2.values, argument));
                    }
                }
                else return gen_0;
            }
            else
            {
                switch (kross(d,2))
                {
                case 1:
                    return gen_0;
                case -1:
                    S = gen_2;
                    break;
                default:
                    S = gen_1;
                    break;
                }
                //Fifth case
                if (e<3)
                {
                    if (e==2 && !gam)
                    {
                        S = gshift(S, -1);
                    }
                    else
                    {
                        S = gmulgs(S, -1);
                    }
                    S = gmul(S, evaluateCharValues(chi2.values, n));
                }
                //First case
                else if (gam>e)
                {
                    S=gshift(S,e-3);
                    if (gam==s+1)
                    {
                        S = gmulgs(S, 3);
                    }
                    else
                    {
                        S = gmulgs(S,-3);
                    }
                }
                else if ((gam==e || gam==e-1) && !chi2.psi2s)
                {
                    S=gshift(S,e-3);
                    if (odd(d)) S = gmulgs(S, -3);
                    S = gmul(S, evaluateCharValues(chi2.values, n));
                }
                //Third case
                else if (s>3 && gam==e)
                {
                    S=gshift(S,e-3);
                    if (!odd(e)) S = gmulgs(S,3);
                }
                //Fourth case
                else if (s>3 && gam==e-1 && odd(e))
                {
                    S=gshift(S,e-3);
                    if (odd(d))
                    {
                        S = gmulgs(S, 3);
                    }
                    else
                    {
                        S = gneg(S);
                    }
                }
                //Default
                else return gen_0;
            }
        }
        i++;
    }

    //Evaluating each prime in turn
    for (; i<psi.chiPfactors.numP; i++)
    {
        TwistAtPrime chiP = psi.chiPfactors.chiPs[i];
        e = chiP.e;
        if (!e) continue;
        p = chiP.p;
        s = chiP.s;
        ptothes = lg(chiP.values)-1;
        //gam = gamma, the power of p in t^2-4n
        gam = getexponent(factorsD, p);
        if (s)
        {
            if (chiP.psi2s)
            {
                //First case
                if (gam> ((e-1) << 1))
                {
                    twonupl = getpower(factorsL, p) << 1;
                    if (odd(gam))
                    {
                        twonupl += (twonupl - ptothes - ptothes/p)/(p-1);
                    }
                    else if (getSQRT(gel(SQRTS,i+1), d)==-1)
                    {
                        twonupl += 2*(twonupl - ptothes - ptothes/p)/(p-1);
                    }
                    S = gmulgs(S,twonupl);
                    continue;
                }
                //Second case
                u = getSQRT(gel(SQRTS,i+1), d);
                u*=L;
                S = gmulgs(S,getpower(factorsL,p));
                if (!t)
                {
                    S = gmul(S,gel(chiP.values,ptothes-1));
                }
                else
                {
                    //chi((t+u)/2)
                    long argument = umodsu(t*(t+u)*getNBar(chiP.barValues, ntimes2)-1,ptothes);
                    S = gmul(S,gel(chiP.values, argument));
                }
                continue;
            }
            //Third case
            else
            {
                if (getSQRT(gel(SQRTS,i+1), n)==-1)
                {
                    if (!odd(gam))
                    {
                        S = gshift(S,1);
                    }
                }
                else
                {
                    if (odd(gam))
                    {
                        S = gneg(S);
                    }
                    else
                    {
                        S = gmul(S, gen_m2);
                    }
                }
                continue;
            }
        }
        //Fourth case
        else if (gam>e-3)
        {
            if (!odd(gam))
            {
                S = gshift(S, 1);
            }
            switch (e)
            {
            case 1:
                S = gneg(S);
                break;
            case 2:
                if(gam) S=gmulgs(S,(1-p)/2);
                break;
            case 3:
                if (gam>1) S = gmulgs(S,1-p*p);
                break;
            default:
                if (!odd(e))
                {
                    if (gam==e-2)
                    {
                        S = gmulgs(S, (p+1)/2);
                    }
                    else
                    {
                        S = gmulgs(S, (1-p*p)/2);
                    }
                }
                else if (gam>e-2) S = gmulgs(S,1-p*p);
                S = gmul(S, powuu(p,e-3));
            }
            continue;
        }
    }
    return S;
}

//Evaluate C2 from the trace formula
static GEN
wt2trivialC2(long N, long n, TwistChar psi, GEN SQRTS)
{
    pari_sp ltop = avma;
    //Start by identifying if the term is 0, and return that if so
    for (long j = psi.chiPfactors.chiPs[0].p==2? 1: 0; j<psi.chiPfactors.numP; j++)
    {
        if(psi.chiPfactors.chiPs[j].s == 0 && psi.chiPfactors.chiPs[j].e>1)
        {
            if (getSQRT(gel(SQRTS,j+1), n)<1)
            {
                return gen_0;
            }
        }
    }
    const long n4 = n << 2;
    GEN factorsN = myfactoru(N);
    //We increment by 2 if n and N are even, or if n is odd and 8 divides N
    long st = (!odd(n) && !odd(N)) || (!(N&7) && odd(n))? 2: 1;
    //Start the term at 0
    GEN c2 = gen_0;
    //t goes up to sqrt(4n)
    long tlimit = usqrt(n4);
    //if n is a perfect square, we don't want t^2=4n, so limit one less
    if (tlimit*tlimit == n4) tlimit--;
    //If we increment by 2, we start on 0 or 1 depending on whether chi_2 is trivial
    for (long t = 0; t <= tlimit; t += st) /* t^2 < 4n */
    {
        long t2 = t*t, D = n4 - t2, L, d;
        d = coredisc2neg(D, &L);
        //t^2-4n = dl^2 where d is the fundamental discriminant
        GEN sh, factorsD = myfactoru(D), factorsL = myfactoru(L);
        //Compute the Spmin term
        sh = wt2trivialSpMin(factorsN, psi, factorsD, factorsL, n, L, d, SQRTS, t);
        if (gequal0(sh))
        {
            continue;
        }
        //If d is -3 or -4 then dividing by w(d) does the following
        //Note, everything is multiplied by 2 for negative t
        if (d == -3)
        {
            sh = gdivgs(sh, 3);
        }
        else if (d == -4)
        {
            sh = gdivgs(sh, 2);
        }
        else
        {
            //otherwise we multiply by h(d)
            sh = gmulgs(sh, myh(d));
        }
        //Multiply by Sp(1,1) terms
        sh = gmul(sh, SP11(psi.Mdash, factorsL, L, d));
        //If t=0 we need to divide by 2
        if (!t)
        {
            sh = gmul2n(sh, -1);
        }
        c2 = gadd(c2, sh);
    }
    return gerepileupto(ltop, c2);
}

//Compute C3 from the trace formula
static GEN
wt2trivialC3(long N, TwistChar psi, GEN Dn)
{
    //If s!=e for any factor, return 0
    for (long i = 0; i<psi.chiPfactors.numP; i++)
    {
        if (psi.chiPfactors.chiPs[i].e != psi.chiPfactors.chiPs[i].psi2s) return gen_0;
    }
    GEN S = gen_0;
    long l=lg(Dn);
    //For each dividor d up to sqrt(n)
    for (long i = 1; i <= (l>>1); i++)
    {
        long d = Dn[i], noverd = Dn[l-i]; /* = n/d */
        GEN t = stoi(d);
        //Evaluate chi at d^2/n and n/d^2
        //Evaluate at each prime
        for (long j = 0; j<psi.chiPfactors.numP; j++)
        {
            TwistAtPrime chiP = psi.chiPfactors.chiPs[j];
            if (chiP.e)
            {
                long d2overn = d*getNBar(chiP.barValues, noverd);
                //Again, real part so (chi(d^2/n)+chi(n/d^2))/2
                GEN chiPd2n = evaluateCharValues(chiP.values, d2overn);
                t = gmul(t, chiPd2n);
            }
        }
        //If d = sqrt(n), divide by 2
        if (d == noverd) t = gmul2n(t,-1);
        S = gadd(S, t);
    }
    return S;
}

//Compute C4 from the formula for S_2^min(N,\psi^2)_\overline{\psi}
//Note, this is always an integer so don't return GEN
static GEN
wt2trivialC4(long n, long Mdash, TwistChar psi, GEN divisorsn)
{
    GEN charpart = gen_1;
    //If psi^2 is not trivial, return 0
    for (long i = 0; i<psi.chiPfactors.numP; i++)
    {
        if (psi.chiPfactors.chiPs[i].psi2s)
        {
            return gen_0;
        }
    }
    for (long i = 0; i<psi.chiPfactors.numP; i++)
    {
        switch (psi.chiPfactors.chiPs[i].e)
        {
        case 0:
            break;
        case 1:
            charpart = gmul(gneg(charpart), evaluateCharValues(psi.chiPfactors.chiPs[i].values, n));
            break;
        default:
            return gen_0;
        }
    }
    long sum = 0;
    for (long i = 1; i < lg(divisorsn); i++)
    {
        long divisor = divisorsn[i];
        /* if gcd(Mdash,d) == 1, add d */
        if (myugcd(psi.gcds, divisor) == 1) sum += divisor;
    }
    return gmulgs(charpart,sum);
}

//Given precomputed square roots and a twist character psi, compute the trace of n from the formula
static GEN wt2trivialTraceByPsi(GEN SQRTS, long n, TwistChar psi, long details)
{
    if (!uissquarefree(psi.gcds[umodsu(n*n,psi.M)+1])) return gen_0;
    pari_sp ltop = avma;
    long Mdash = psi.Mdash;
    GEN divisorsn = divisorsu(n);
    //Compute C4
    GEN t = wt2trivialC4(n, Mdash, psi, divisorsn);
    //Compute C1
    GEN a = wt2trivialC1(Mdash, psi, n);
    //If C4 was not 0, add it
    if (!gequal0(t)) a = gadd(a,t);
    //Compute C2 if non-zero
    GEN b = wt2trivialC2(Mdash, n, psi, SQRTS);
    //Compute C3
    b = gadd(b, wt2trivialC3(psi.M, psi, divisorsn));
    //Combine C1-C2-C3+C4
    b = gsub(a,b);
    //twists from 0
    for (long i = 0; i<psi.chiPfactors.numP; i++)
    {
        if (!psi.chiPfactors.chiPs[i].e)
        {
            b = gmul(b, evaluateCharValues(psi.chiPfactors.chiPs[i].values, n));
        }
    }

    if (details)
    {
        pari_printf("lower level is %ld\n", psi.Mdash);
        pari_printf("char values are %Ps\n", psi.chiPfactors.chiPs[0].values);
        pari_printf("C1 is %Ps\n", wt2trivialC1(Mdash, psi, n));
        pari_printf("C2 is %Ps\n", wt2trivialC2(Mdash, n, psi, SQRTS));
        pari_printf("C3 is %Ps\n", wt2trivialC3(psi.M, psi, divisorsn));
        pari_printf("C4 is %Ps\n", wt2trivialC4(n, Mdash, psi, divisorsn));
        pari_printf("trace is %Ps\n", b);
    }
    return gerepileupto(ltop, b);
}

//For given conrey log stat at a given p, initialise all the required statistics for chi_p
TwistAtPrime
getTwistChiP(GEN charGroup, long p, long e, long stat, long varnum)
{
    TwistAtPrime chiP;
    chiP.p = p;
    if (stat<0)
    {
        //s is the exponent of the conductor
        chiP.s = e/2;
        //psi2s is the exponent of psi^2
        chiP.psi2s = 0;
        //e is the exponent of the level
        chiP.e = -1-stat;
        GEN poldetails = getMaximalChipMod(charGroup, varnum);
        //a vector of the characters values
        chiP.values = getQuadraticValues(p, poldetails);
        //order of the character
        chiP.order = gen_2;
    }
    else if (!stat)
    {
        chiP.e = e;
        chiP.s = 0;
        chiP.psi2s = 0;
        chiP.order=gen_1;
        chiP.values = mkvec(gen_1);
    }
    else
    {
        chiP.e = stat;
        chiP.s = stat;
        chiP.psi2s = stat;
        GEN poldetails = getMaximalChipMod(charGroup, varnum);
        chiP.values = getTwistCharValues(p, poldetails);
        chiP.order = gel(charGroup,1);
    }
    return chiP;
}

//Statistics for chi_2
TwistAtPrime
getTwistChi2(GEN charGroup, long e, long stat, long varnum)
{
    TwistAtPrime chiP;
    chiP.p = 2;

    //Stat = 0 indicates no twist
    if (!stat)
    {
        chiP.e = e;
        chiP.s = 0;
        chiP.psi2s = 0;
        chiP.order=gen_1;
        chiP.values = mkvec(gen_1);
    }
    //stat<0 indicates a twist by a quadratic character
    //The level twisted from, M, is given by -1-stat
    else if (stat<0)
    {
        chiP.s = e/2;
        chiP.psi2s = 0;
        chiP.e = -1-stat;
        //If e is 6 we are twisting by level 8
        if (e==6)
        {
            if(stat!=-6)
            {
                GEN c2var = pol_x(1);
                chiP.values = mkvecn(8, gen_1, gen_0, c2var, gen_0, gen_m1, gen_0, gmul(gen_m1,c2var), gen_0);
            }
            else
            {
                chiP.values = mkvecn(8, gen_1, gen_0, gen_m1, gen_0, gen_m1, gen_0, gen_1, gen_0);
            }
        }
        //Else we're twisting by level 4
        else
        {
            chiP.values = mkvecn(4, gen_1, gen_0, gen_m1, gen_0);
        }
        chiP.order = gen_2;
    }
    //Finally, we have a twist stat gives nu_2(M) and of course the conductor of the
    //character must be sqrt(N)
    else
    {
        chiP.e = stat;
        chiP.s = e/2;
        chiP.psi2s = chiP.s-1;
        //yvar indicates the C4 part of the character. It will be embedded to +/-1
        GEN yvar = pol_x(1);
        //Multiple of cyclotomic, see odd prime case
        GEN pol = gsub(pol_xn(itos(gel(charGroup,1))/2, varnum+1),gen_1);
        pol = gdiv(pol,gsub(pol_x(varnum+1),gen_1));
        GEN poldetails = mkvec3(charGroup,pol_x(varnum+1), pol);
        chiP.values = getTwistCharValues(2, poldetails);
        for (long i=3; i<lg(chiP.values); i+=4)
        {
            if (stat==e/2-1)
            {
                gel(chiP.values,i) = gmul(yvar,gel(chiP.values,lg(chiP.values)-i-1));
            }
            else
            {
                gel(chiP.values,i) = gel(chiP.values,lg(chiP.values)-i-1);
            }
        }

        chiP.order = gshift(gel(charGroup,1),-1);
    }
    return chiP;
}

//Create the TwistChar from specified stats
TwistChar
initialiseWt2TwistChar(long M, GEN stats, GEN groups)
{
    GEN factors = myfactoru(M);
    GEN primes = gel(factors,1);
    GEN exponents = gel(factors,2);
    long mdash = 1;
    long len = lg(primes);
    //The character is really a vector with one variable and cyclotomic polynomial for each character
    TwistChar character;
    character.M = M;
    character.chiPfactors.numP = len-1;
    long i =1;
    if (primes[1]==2)
    {
        character.chiPfactors.chiPs[0] = getTwistChi2(gel(groups,1), exponents[1], stats[1], i);
        if (character.chiPfactors.chiPs[0].e)
        {
            mdash *= upowuu(2,character.chiPfactors.chiPs[0].e);
        }
        i++;
    }
    for (; i<len ; i++)
    {
        character.chiPfactors.chiPs[i-1] = getTwistChiP(gel(groups,i), primes[i], exponents[i], stats[i], i);
        if (character.chiPfactors.chiPs[i-1].e)
        {
            mdash *= upowuu(primes[i],character.chiPfactors.chiPs[i-1].e);
        }
    }
    character.Mdash = mdash;
    for (i=0; i<len-1; i++)
    {
        TwistAtPrime chiP = character.chiPfactors.chiPs[i];
        long chiN = lg(chiP.values)-1;
        character.chiPfactors.chiPs[i].barValues = const_vecsmall(chiN, 0);
        for (long ind = 2; ind<chiN; ind++)
        {
            GEN val = gel(chiP.values, ind);
            if (gequal0(val)) continue;
            long j = itos(gmodgs(sstoQ(1,ind), chiN));
            character.chiPfactors.chiPs[i].barValues[j] = ind;
        }
        character.chiPfactors.chiPs[i].barValues[1] = 1;
    }
    return character;
}

//Return a vector of all labels of required psi to twist to N, given the factors of N
GEN
getRequiredStats(GEN factors)
{
    pari_sp ltop = avma;
    GEN requiredStats = mkvec(gcopy(gel(factors,2)));
    GEN option;
    long l = lg(gel(factors,1));
    long start = 1;
    //Start with the character where nothing twists
    for (long i = 1; i<l; i++)
    {
        gel(requiredStats,1)[i]=0;
    }
    //If the level is even, the twist cases are a little different
    if (gel(factors,1)[1]==2)
    {
        long e = gel(factors,2)[1];
        //If the power of 2 is even
        if (!odd(e))
        {
            switch (e)
            {
            //Nothing to 4
            case 2:
                break;
            //To 64 we have the same as to 16 but all twists are by a level 8 character
            //and we include an additional twist from level 32.
            //The numbers here are -v-1 where v is nu_2(M)
            case 6:
                option = gcopy(gel(requiredStats, 1));
                option[1]=-6;
                requiredStats = vec_append(requiredStats, option);
            //To 16 we have -1, -2, -3 and -4 indicating twists by the level 4
            //character from 1, 2, 4 and 8 respectively
            case 4:
                option = gcopy(gel(requiredStats, 1));
                option[1]=-1;
                requiredStats = vec_append(requiredStats, option);
                option = gcopy(gel(requiredStats, 1));
                option[1]=-2;
                requiredStats = vec_append(requiredStats, option);
                option = gcopy(gel(requiredStats, 1));
                option[1]=-3;
                requiredStats = vec_append(requiredStats, option);
                gel(requiredStats,1)[1]=-4;
                break;
            //In general, we will twist from e-1, e-2 and e/2-1
            default:
                option = gcopy(gel(requiredStats, 1));
                option[1]=e-1;
                requiredStats = vec_append(requiredStats, option);
                option = gcopy(gel(requiredStats, 1));
                option[1]=e-2;
                requiredStats = vec_append(requiredStats, option);
                gel(requiredStats,1)[1]=e/2-1;
                break;
            }
        }
        start++;
    }
    //In the specific case where the factor at 3 is 9, we don't include non-quadratic character
    //(as there isn't one of conductor 3)
    if (gel(factors,1)[start]==3 && gel(factors,2)[start]==2)
    {
        GEN currentOptions = gcopy(requiredStats);
        for (long j = 1; j<lg(currentOptions); j++)
        {
            option = gcopy(gel(currentOptions, j));
            option[start]=-1;
            requiredStats = vec_append(requiredStats, option);
            option = gcopy(gel(currentOptions, j));
            option[start]=-2;
            requiredStats = vec_append(requiredStats, option);
        }
        start++;
    }
    //For all other odd primes, we add the full conductor twist, and if needed the quadratic twist from
    //e=1 and e=0
    for (long i = start; i<l; i++)
    {
        GEN currentOptions = gcopy(requiredStats);
        long e = gel(factors,2)[i];
        if (!odd(e))
        {
            //Add full conductor twist
            for (long j = 1; j<lg(currentOptions); j++)
            {
                option = gcopy(gel(currentOptions, j));
                option[i]=e/2;
                requiredStats = vec_append(requiredStats, option);
            }
            if (e==2)
            {
                for (long j = 1; j<lg(currentOptions); j++)
                {
                    //Add quadratic twist from e=0 (denoted -2) and e=1 (denoted -1)
                    option = gcopy(gel(currentOptions, j));
                    option[i]=-1;
                    requiredStats = vec_append(requiredStats, option);
                    option = gcopy(gel(currentOptions, j));
                    option[i]=-2;
                    requiredStats = vec_append(requiredStats, option);
                }
            }
        }
    }
    return gerepilecopy(ltop, requiredStats);
}

long getEmbeddedChipOrder(TwistChar psi, GEN embedding, long pindex)
{
    long i = 1;

    GEN order = gen_1;
    //Treat p=2 slightly differently
    if (psi.chiPfactors.chiPs[0].p==2)
    {
        if(psi.chiPfactors.chiPs[0].s>2 && (psi.chiPfactors.chiPs[0].e<4 || psi.chiPfactors.chiPs[0].e==psi.chiPfactors.chiPs[0].s-1))
        {
            i++;
            order = gdivgs(psi.chiPfactors.chiPs[0].order, embedding[2]);
        }
        else if(embedding[1])
        {
            order = gdivgs(psi.chiPfactors.chiPs[0].order, embedding[1]);
        }
        if(psi.chiPfactors.chiPs[0].psi2s>3 && psi.chiPfactors.chiPs[0].psi2s<psi.chiPfactors.chiPs[0].e)
        {
            order = gshift(order,-1);
        }
        if(psi.chiPfactors.chiPs[0].psi2s>4 && psi.chiPfactors.chiPs[0].psi2s<psi.chiPfactors.chiPs[0].e)
        {
            order = gshift(order,-1);
        }
        if(pindex==0) return itos(order);
    }
    return itos(gdivgs(psi.chiPfactors.chiPs[pindex].order, ugcdui(embedding[pindex+i], psi.chiPfactors.chiPs[pindex].order)));
}

//Create a vector of all embeddings of a master character psi
GEN
listEmbeddings(TwistChar psi)
{
    pari_sp ltop = avma;
    GEN embeddings = mkvec(mkvecsmalln(0));
    long has2 = 0;
    if (psi.chiPfactors.chiPs[0].p==2  && psi.chiPfactors.chiPs[0].s>2 && (psi.chiPfactors.chiPs[0].e<4 || psi.chiPfactors.chiPs[0].e == psi.chiPfactors.chiPs[0].s-1))
    {
        embeddings = mkvec2(mkvecsmall(0),mkvecsmall(1));
        has2 = 1;
    }
    for (long i = 0; i<psi.chiPfactors.numP; i++)
    {
        TwistAtPrime psiP = psi.chiPfactors.chiPs[i];
        long p = psiP.p;
        if (gequal1(psiP.order))
        {
            for (long j = 1; j<lg(embeddings); j++)
            {
                gel(embeddings,j) = vecsmall_append(gel(embeddings,j), 0);
            }
            continue;
        }
        if (p==2 || (itos(psiP.order)<4))
        {
            for (long j = 1; j<lg(embeddings); j++)
            {
                gel(embeddings,j) = vecsmall_append(gel(embeddings,j), 1);
            }
            continue;
        }
        GEN newEmbeddings = cgetg(1,t_VEC);
        GEN covered = cgetg(1, t_VEC);
        for (long embeddingIndex = 1; embeddingIndex<lg(embeddings); embeddingIndex++)
        {
            GEN oldEmbedding = gel(embeddings, embeddingIndex);
            long leftOrder = 1;
            for(long j = 0; j<i; j++)
            {
                if(gequal1(psi.chiPfactors.chiPs[j].order)) continue;
                long embeddedOrder = getEmbeddedChipOrder(psi, oldEmbedding, j);
                leftOrder = ulcm(leftOrder, embeddedOrder);
            }
            long thisOrder = itos(psiP.order);
            for (long thisembed = 1; thisembed<(thisOrder>>1); thisembed++)
            {
                if(!umodsu(thisembed, p)) continue;
                //check covered for embeddingWouldBe
                GEN embeddingWouldBe = vecsmall_append(oldEmbedding, thisembed);
                long embeddedOrder = ulcm(leftOrder, getEmbeddedChipOrder(psi, embeddingWouldBe, i));
                long alreadyCovered = 0;
                for(long coveredi = 1; coveredi<lg(covered); coveredi++){
                    if(gequal(gel(covered,coveredi), embeddingWouldBe)){
                        alreadyCovered = 1;
                        break;
                    }
                }
                if (alreadyCovered) continue;

                //Append all galois orbit to covered
                covered = vec_append(covered, embeddingWouldBe);
                GEN alt = gcopy(embeddingWouldBe);

                for(long galoispow = 2; galoispow<=embeddedOrder/2; galoispow++)
                {
                    for(long pn = 1; pn<lg(embeddingWouldBe)-has2; pn++)
                    {
                        if(!psi.chiPfactors.chiPs[pn-1].s) continue;
                        long chiporder = itos(psi.chiPfactors.chiPs[pn-1].order);
                        alt[pn+has2] = Fl_mul(embeddingWouldBe[pn+has2],galoispow,chiporder);
                        if(chiporder<(alt[pn+has2]<<1))
                        {
                            alt[pn+has2] = chiporder-alt[pn+has2];
                        }
                    }
                    if(gequal(alt, embeddingWouldBe)) break;
                    if(ugcd(galoispow, embeddedOrder)==1){
                        covered = vec_append(covered, gcopy(alt));
                    }
                }
                //Append newembedding
                newEmbeddings = vec_append(newEmbeddings, embeddingWouldBe);
            }
        }
        embeddings = shallowcopy(newEmbeddings);

    }
    return gerepilecopy(ltop, embeddings);
}

GEN getGaloisPows(long order, TwistChar psi, GEN embedding)
{
    GEN galoisPows = mkvecsmall(1);
    if(order==5 || order>6)
    {
        long has2 = lg(embedding)-1>psi.chiPfactors.numP;
        GEN covered = mkvec(embedding);
        GEN alt = gcopy(embedding);
        for(long galoisPow = 2; galoisPow<=order/2; galoisPow++)
        {
            if(ugcd(galoisPow,order)!=1) continue;

            for(long pn = 1; pn<lg(embedding)-has2; pn++)
            {
                if(!psi.chiPfactors.chiPs[pn-1].s) continue;
                long chiporder = itos(psi.chiPfactors.chiPs[pn-1].order);
                alt[pn+has2] = Fl_mul(embedding[pn+has2],galoisPow,chiporder);
                if(chiporder<(alt[pn+has2]<<1))
                {
                    alt[pn+has2] = chiporder-alt[pn+has2];
                }
            }
            long alreadyCovered = 0;
            for(long coveredi = 1; coveredi<lg(covered); coveredi++)
            {
                if(gequal(gel(covered,coveredi), alt))
                {
                    alreadyCovered = 1;
                    break;
                }
            }
            if (alreadyCovered) continue;

            galoisPows = vecsmall_append(galoisPows, galoisPow);

            //Add to covered
            covered = vec_append(covered, gcopy(alt));
        }


    }
    return galoisPows;
}

GEN OLDgetGaloisPows(long order, TwistChar psi, GEN embedding)
{
    GEN galoisPows = mkvecsmall(1);
    if(order==5 || order>6)
    {
        long has2 = lg(embedding)-1>psi.chiPfactors.numP;
        for(long galoisPow = 2; galoisPow<order; galoisPow++)
        {
            long useThisPow = 1;
            if(ugcd(galoisPow,order)!=1) continue;
            for(long pn = 0; pn<psi.chiPfactors.numP; pn++)
            {
                if(!psi.chiPfactors.chiPs[pn].s) continue;
                long chiporder = itos(psi.chiPfactors.chiPs[pn].order);
                long embeddingWouldBe = Fl_mul(embedding[pn+1+has2], galoisPow, chiporder);
                if(chiporder-embeddingWouldBe < embeddingWouldBe)
                {
                    useThisPow = 0;
                    break;
                }
            }
            if (useThisPow)
            {
                galoisPows = vecsmall_append(galoisPows, galoisPow);
            }

        }
    }
    return galoisPows;
}


//Given a character psi and embedding, return the order of the character
long getEmbeddedCharOrder(TwistChar psi, GEN embedding)
{
    long i = 1;
    long start = 0;

    GEN order = gen_1;
    //Treat p=2 slightly differently
    if (psi.chiPfactors.chiPs[0].p==2)
    {
        start++;
        if(psi.chiPfactors.chiPs[0].s>2 && (psi.chiPfactors.chiPs[0].e<4 || psi.chiPfactors.chiPs[0].e==psi.chiPfactors.chiPs[0].s-1))
        {
            i++;
            order = gdivgs(psi.chiPfactors.chiPs[0].order, embedding[2]);
        }
        else if(embedding[1])
        {
            order = gdivgs(psi.chiPfactors.chiPs[0].order, embedding[1]);
        }
        if(psi.chiPfactors.chiPs[0].psi2s>3 && psi.chiPfactors.chiPs[0].psi2s<psi.chiPfactors.chiPs[0].e)
        {
            order = gshift(order,-1);
        }
        if(psi.chiPfactors.chiPs[0].psi2s>4 && psi.chiPfactors.chiPs[0].psi2s<psi.chiPfactors.chiPs[0].e)
        {
            order = gshift(order,-1);
        }
    }
    for (long j = start; j<psi.chiPfactors.numP; j++)
    {
        if (embedding[j+i])
        {
            order = lcmii(order, gdivgs(psi.chiPfactors.chiPs[j].order, ugcdui(embedding[j+i], psi.chiPfactors.chiPs[j].order)));
        }
    }
    return itos(order);
}

//Embed polynomial trace into single-variable polynomial
GEN embedTrace(GEN element, GEN embedding, TwistChar psi, GEN order)
{
    pari_sp ltop = avma;
    GEN embeddedElement = gcopy(element);
    long i = 1;
    if (psi.chiPfactors.chiPs[0].p==2  && psi.chiPfactors.chiPs[0].s>2 && (psi.chiPfactors.chiPs[0].e<4 || psi.chiPfactors.chiPs[0].e == psi.chiPfactors.chiPs[0].s-1))
    {
        if (embedding[1]==0)
        {
            embeddedElement = gsubst(embeddedElement, 1, gen_1);
        }
        else
        {
            embeddedElement = gsubst(embeddedElement, 1, gen_m1);
        }
        i++;
    }
    if (gequal1(order)) return embeddedElement;
    long vt = fetch_user_var("t");
    GEN cyclopol = polcyclo(itos(order), vt);

    for (long j=i; j<lg(embedding); j++)
    {
        if (embedding[j])
        {
            char varname[6];
            sprintf(varname, "t%ld", j-i+2);
            embeddedElement = gsubst(embeddedElement, j+2-i, pol_xn(itos(gdiv(gmulgs(order,embedding[j]),psi.chiPfactors.chiPs[j-i].order)),vt));
            embeddedElement = gsubst(embeddedElement, fetch_user_var(varname), pol_xn(itos(gdiv(gmulgs(order,embedding[j]),psi.chiPfactors.chiPs[j-i].order)),vt));
        }
    }
    if (typ(embeddedElement)==t_POL)
    {
        embeddedElement = RgX_rem(embeddedElement, cyclopol);
        if (poldegree(embeddedElement, vt)<1)
        {
            embeddedElement = constant_coeff(embeddedElement);
        }
    }
    return gerepileupto(ltop, embeddedElement);
}

GEN getFullOrbit(GEN singleElt, GEN substitutes)
{
    pari_sp ltop = avma;
    if(typ(singleElt)==t_POL){
        GEN val = gcopy(singleElt);
        for(long powi = 2; powi<lg(substitutes); powi++){
            val = gadd(val, QX_ZXQV_eval(singleElt, gel(substitutes,powi), NULL));
        }
        val = constant_coeff(val);
        return gerepileupto(ltop, val);
                    }
        return gmulgs(singleElt, lg(substitutes)-1);
}

//Compute a twist-space for weight 2
GEN computeBasis(GEN stat, long M, GEN SQRTS, TwistChar psi, long details)
{
    pari_sp ltop = avma;
    //Compute the multivariate trace form
    GEN traceForm = wt2trivialTraceByPsi(SQRTS, 1, psi, 0);
    if (gequal0(traceForm))
    {
        return NULL;
    }

    GEN newbasis = mkvec3(stat, NULL, zerovec(0));

    GEN embeddings = listEmbeddings(psi);

    traceForm = mkvec(traceForm);

    //For each embedding of the master character
    for (long i=1; i<lg(embeddings); i++)
    {
        GEN embedding = gel(embeddings, i);
        //Embed the master polynomial's first coeff to get the dimension
        long order = getEmbeddedCharOrder(psi, embedding);
        GEN galoisPows = getGaloisPows(order, psi, embedding);
        long vt = fetch_user_var("t");
        GEN cycloPol = polcyclo(order, vt);
        GEN substitutes = cgetg(lg(galoisPows),t_VEC);
        for(long j = 1; j<lg(galoisPows); j++){
            gel(substitutes, j) = ZXQ_powers(pol_xn(galoisPows[j],vt), degree(cycloPol), cycloPol);
        }
        GEN dim = embedTrace(gel(traceForm, 1), embedding, psi, stoi(order));
        long numElts = itos(dim)*(lg(galoisPows)-1);
        if (!numElts) continue;
        //The number of coefs required. First try number of elements
        long numcoefs = numElts;
        GEN embeddedTraceForm = const_vec(numcoefs, stoi(-999));
        //Hecke operators used to create basis from trace form
        GEN operatorsUsed = mkvecsmall(1);
        GEN basisCoefs = zeromat(numcoefs, 1);
        gel(embeddedTraceForm, 1) = stoi(numElts);
        gcoeff(basisCoefs, 1, 1) = gel(embeddedTraceForm,1);
        pari_sp aboveCalculations = avma;
        //If we need more coefficients for the traceForm or embeddedTraceFom, add the needed coefficients
        if (lg(traceForm)<=numcoefs)
        {
            traceForm = shallowconcat(traceForm, const_vec(numcoefs+1-lg(traceForm), stoi(-999)));
        }
        for (long n = 2; n<=numcoefs; n++)
        {
            //If the entry is NULL, compute
            if (gequal(gel(traceForm, n),stoi(-999)))
            {
                gel(traceForm, n) = wt2trivialTraceByPsi(SQRTS, n, psi, 0);
            }
            if (gequalgs(gel(embeddedTraceForm, n),-999))
            {
                gel(embeddedTraceForm, n) = embedTrace(gel(traceForm, n), gel(embeddings,i), psi, stoi(order));
                if(lg(galoisPows)>2){
                    gel(embeddedTraceForm,n) = getFullOrbit(gel(embeddedTraceForm, n), substitutes);
                }
            }
            gcoeff(basisCoefs,n,1) = gel(embeddedTraceForm, n);
        }
        //Hit the traceform with hecke operators
        long onlyTriedOnce = 1;
        for (long m = 2; lg(basisCoefs)<=numElts; m++)
        {
            if (!uissquarefree(psi.gcds[umodsu(m*m,M)+1])) continue;
            if (lg(traceForm)<=numcoefs*m)
            {
                traceForm = shallowconcat(traceForm, const_vec(numcoefs*m+1-lg(traceForm), stoi(-999)));
            }
            if (lg(embeddedTraceForm)<=numcoefs*m)
            {
                embeddedTraceForm = shallowconcat(embeddedTraceForm, const_vec(numcoefs*m+1-lg(embeddedTraceForm), stoi(-999)));
            }
            GEN element = zeromat(numcoefs,1);
            for (long n = 1; n<=numcoefs; n++)
            {
                long mn=m*n;
                GEN entry = gen_0;
                long gcdmn = cgcd(m,n);
                GEN divsmn = divisorsu(gcdmn);
                for (long divi=1; divi<lg(divsmn); divi++)
                {
                    long r = divsmn[divi];
                    if (ugcd(r, M)!=1) continue;
                    long mnoverr2 = mn/r/r;
                    if (gequal(gel(traceForm, mnoverr2),stoi(-999)))
                    {
                        gel(traceForm, mnoverr2) = wt2trivialTraceByPsi(SQRTS, mnoverr2, psi, 0);
                    }
                    if (gequal(gel(embeddedTraceForm, mnoverr2),stoi(-999)))
                    {
                        gel(embeddedTraceForm, mnoverr2) = embedTrace(gel(traceForm, mnoverr2), gel(embeddings,i), psi, stoi(order));
                        if(lg(galoisPows)>2){
                        gel(embeddedTraceForm,mnoverr2) = getFullOrbit(gel(embeddedTraceForm,mnoverr2), substitutes);
                }
                    }
                    entry = gadd(entry, gmulgs(gel(embeddedTraceForm, mnoverr2), r));
                }
                gcoeff(element, n, 1) = entry;
            }
            //If the element isn't 0, and it doesn't intersect with the already existing coefs
            if (lg(ZabM_ker(shallowconcat(basisCoefs, element), cycloPol, order))==1)
            {
                basisCoefs = concat(basisCoefs, element);
                operatorsUsed = vecsmall_append(operatorsUsed, m);
                if(details) pari_printf("now have %ld elements of %ld needed\n", lg(basisCoefs)-1, numElts);
                gerepileall(aboveCalculations, 4, &basisCoefs, &operatorsUsed, &traceForm, &embeddedTraceForm);
                onlyTriedOnce = 1;
            }
            else
            {
                //Perhaps need additional coefficients
                if (onlyTriedOnce)
                {
                    long diff = 5;
                    basisCoefs = vconcat(basisCoefs, zeromat(diff,lg(basisCoefs)-1));
                    numcoefs+=diff;
                    if (lg(traceForm)<=numcoefs*operatorsUsed[lg(basisCoefs)-1])
                    {
                        traceForm = shallowconcat(traceForm, const_vec(numcoefs*operatorsUsed[lg(basisCoefs)-1]+1-lg(traceForm), stoi(-999)));
                    }
                    if (lg(embeddedTraceForm)<=numcoefs*operatorsUsed[lg(basisCoefs)-1])
                    {
                        embeddedTraceForm = shallowconcat(embeddedTraceForm, const_vec(numcoefs*operatorsUsed[lg(basisCoefs)-1]+1-lg(embeddedTraceForm), stoi(-999)));
                    }
                    for (long furthern = numcoefs+1-diff; furthern<=numcoefs; furthern++){
                    for (long j = 1; j< lg(basisCoefs); j++)
                    {
                        long mn=furthern*operatorsUsed[j];
                        GEN entry = gen_0;
                        long gcdmn = cgcd(furthern, operatorsUsed[j]);
                        GEN divsmn = divisorsu(gcdmn);
                        for (long divi=1; divi<lg(divsmn); divi++)
                        {
                            long r = divsmn[divi];
                            if (ugcd(r, M)!=1) continue;
                            long mnoverr2 = mn/r/r;
                            if (gequal(gel(traceForm, mnoverr2),stoi(-999)))
                            {
                                gel(traceForm, mnoverr2) = wt2trivialTraceByPsi(SQRTS, mnoverr2, psi, 0);
                            }
                            if (gequal(gel(embeddedTraceForm, mnoverr2),stoi(-999)))
                            {
                                gel(embeddedTraceForm, mnoverr2) = embedTrace(gel(traceForm, mnoverr2), gel(embeddings,i),psi, stoi(order));
                                if(lg(galoisPows)>2){
                                        gel(embeddedTraceForm, mnoverr2) = getFullOrbit(gel(embeddedTraceForm, mnoverr2), substitutes);
                                }
                            }
                            entry = gadd(entry, gmulgs(gel(embeddedTraceForm, mnoverr2), r));
                        }
                        gcoeff(basisCoefs, furthern, j) = entry;
                    }
                    }
                    m--;
                    onlyTriedOnce = 0;
                } else {
                    onlyTriedOnce = 1;
                }
            }
        }
        //add embedded basis to newbasis
        GEN embeddedBasis = mkvec2(embedding, operatorsUsed);
        gel(newbasis, 3) = shallowconcat(gel(newbasis, 3), mkvec(embeddedBasis));
    }
    if(lg(gel(newbasis,3))==1) return NULL;
    gel(newbasis, 2) = traceForm;
    return gerepilecopy(ltop, newbasis);
}

GEN getAllGroups(long N)
{
    GEN factors = myfactoru(N);
    GEN allgroups = zerovec(lg(gel(factors,1))-1);
    for (long i=1; i<lg(allgroups); i++)
    {
        if (!odd(gel(factors,2)[i]))
        {
            gel(allgroups,i)=getCharGroup(gel(factors,1)[i],gel(factors,2)[i]/2);
        }
    }
    return allgroups;
}

//Initialise the weight 2 space. This is a vector of all the information stored on weight 2 spaces
GEN
initialiseWt2Space(long M, long details)
{
    pari_sp ltop = avma;
    GEN spaces = cgetg(1, t_VEC);
    GEN factors = myfactoru(M);
    GEN stats = getRequiredStats(factors);
    //The square roots for M
    GEN sqrts = mksqr(M);
    //All of the groups for each prime (used to create the chi_p)
    GEN allgroups = getAllGroups(M);
    for(long i = 1; i<lg(stats); i++)
    {
        //For each twist psi, generate the space of twisted elements
        GEN stat = gel(stats,i);
        TwistChar psi = initialiseWt2TwistChar(M, stat, allgroups);
        psi.gcds = mkgcd(M);
        if(details) pari_printf("computing basis for char %Ps\n", gel(stats,i));
        GEN twistSpace = computeBasis(stat, M, sqrts, psi, details);
        //If the twistspace isn't empty, append to the space
        if (twistSpace != NULL)
        {
            spaces = vec_append(spaces, twistSpace);

        }
    }
    spaces = vec_append(spaces, gen_0);
    char filename[20];
    char dummyfilename[20];
    sprintf(filename, "wt2spaces/%ld.txt", M);
    sprintf(dummyfilename, "dummies2/%ld.txt", M);
    FILE *dummy_file = fopen(dummyfilename, "w");
    flock(fileno(dummy_file), LOCK_EX);
    FILE *out_file = fopen(filename, "w");

    pari_fprintf(out_file, "%Ps\n", spaces);
    fclose(out_file);
    flock(fileno(dummy_file), LOCK_UN);
    fclose(dummy_file);
    return gerepilecopy(ltop, spaces);
}

//Given embedded traceform, recover the basis elements between first and last coefs
GEN getBasisFromTrace(TwistChar psi, GEN SQRTS, GEN minspace, long firstCoef, long lastCoef)
{
    pari_sp ltop = avma;
    long offset = firstCoef-1;
    GEN basis = cgetg(1,t_MAT);
    GEN traceform = gel(minspace,2);
    for (long i =1; i<lg(gel(minspace,3)); i++)
    {
        GEN embeddedBasis = gel(gel(minspace,3),i);
        long order = getEmbeddedCharOrder(psi, gel(embeddedBasis,1));
        GEN galoisPows = getGaloisPows(order, psi, gel(embeddedBasis,1));
        long vt = fetch_user_var("t");
        GEN cycloPol = polcyclo(order, vt);
        GEN substitutes = cgetg(lg(galoisPows),t_VEC);
        for(long j = 1; j<lg(galoisPows); j++){
            gel(substitutes, j) = ZXQ_powers(pol_xn(galoisPows[j],vt), degree(cycloPol), cycloPol);
        }

        GEN operatorsUsed = gel(embeddedBasis, 2);
        GEN embeddedTraceForm = const_vec(lg(gel(minspace,2))-1,NULL);
        GEN divsr;

        //Get all the embedded trace form we need
        for (long n = firstCoef; n<=lastCoef; n++)
        {
            long indicator = myugcd(psi.gcds, n*n);
            if (!uissquarefree(indicator))
            {
                continue;
            }
            for (long j = 1; j<lg(operatorsUsed); j++)
            {
                long nm = n*operatorsUsed[j];
                divsr = divisorsu(ugcd(n,operatorsUsed[j]));
                for (long divi=1; divi<lg(divsr); divi++)
                {
                    long r = divsr[divi];
                    if (myugcd(psi.gcds, r)!=1) continue;
                    long nmoverr2 = nm/r/r;
                    if(gel(embeddedTraceForm, nmoverr2)==NULL)
                    {
                        gel(embeddedTraceForm, nmoverr2) = embedTrace(gel(traceform,nmoverr2), gel(embeddedBasis, 1), psi, stoi(order));
                        if(lg(galoisPows)>2){
                                gel(embeddedTraceForm, nmoverr2) = getFullOrbit(gel(embeddedTraceForm,nmoverr2), substitutes);
                }
                    }
                }
            }
        }
        //if(psi.M==289 && psi.Mdash==17) pari_printf("embeddedTraceForm is %Ps\n", vecslice(embeddedTraceForm,1,10));


        GEN basisCoefs = zeromatcopy(lastCoef-offset, lg(operatorsUsed)-1);

        for (long n = firstCoef; n<=lastCoef; n++)
        {
            long indicator = myugcd(psi.gcds, n*n);
            if (!uissquarefree(indicator))
            {
                continue;
            }
            long index = n-offset;
            for (long j = 1; j<lg(basisCoefs); j++)
            {
                long nm = n*operatorsUsed[j];
                divsr = divisorsu(ugcd(n,operatorsUsed[j]));
                for (long divi=1; divi<lg(divsr); divi++)
                {
                    long r = divsr[divi];
                    if (myugcd(psi.gcds, r)!=1) continue;
                    long nmoverr2 = nm/r/r;
                    gcoeff(basisCoefs,index,j) = gadd(gcoeff(basisCoefs, index, j), gmulgs(gel(embeddedTraceForm, nmoverr2), r));
                }
            }
        }
        basis = shallowconcat(basis, basisCoefs);
    }
    return gerepilecopy(ltop, basis);
}

//Given a wt2 trivial space, expand all basis elements up to coefficient lim
GEN expandBasisUpTo(long N, GEN spaces, long lim)
{
    pari_sp ltop = avma;
    GEN allgroups = getAllGroups(N);
    GEN sqrts = mksqr(N);
    GEN gcds = mkgcd(N);
    for (long spacei = 1; spacei<lg(spaces)-1; spacei++)
    {
        GEN minspace = gel(spaces, spacei);
        pari_sp beforeTraceComputations = avma;
        GEN traceform = gel(minspace,2);
        TwistChar psi = initialiseWt2TwistChar(N, gel(gel(spaces,spacei),1), allgroups);
        psi.gcds = gcds;

        long numKnown = lg(traceform)-1;
        for (long i = 1; i<lg(gel(minspace,3)); i++)
        {
            GEN embeddedBasis = gel(gel(minspace,3),i);
            GEN operatorsUsed = gel(embeddedBasis, 2);
            long altKnown = (lg(traceform)-1)/operatorsUsed[lg(operatorsUsed)-1];
            if (altKnown<numKnown) numKnown = altKnown;
        }

        if (numKnown>=lim) continue;

        for (long i =1; i<lg(gel(minspace,3)); i++)
        {
            GEN embeddedBasis = gel(gel(minspace,3),i);
            GEN operatorsUsed = gel(embeddedBasis, 2);

            long maxneeded = lim*operatorsUsed[lg(operatorsUsed)-1];
            if (lg(traceform) <= maxneeded)
            {
                traceform = shallowconcat(traceform, const_vec(maxneeded+1-lg(traceform), stoi(-999)));
            }
            for(long operatorj = 1; operatorj<lg(operatorsUsed); operatorj++)
            {
                for (long n = numKnown+1; n<=lim; n++)
                {
                    long nm = n*operatorsUsed[operatorj];
                    GEN divs = divisorsu(ugcd(n,operatorsUsed[operatorj]));
                    for(long divi = 1; divi<lg(divs); divi++)
                    {
                        long r = divs[divi];
                        long nmoverr2 = nm/r/r;
                        if (!gequal(gel(traceform, nmoverr2), stoi(-999))) continue;
                        long indicator = myugcd(psi.gcds, nmoverr2*nmoverr2);

                        if (!uissquarefree(indicator))
                        {
                            gel(traceform,nmoverr2)=gen_0;
                            continue;
                        }
                        //If the first coeff is 1, we can use multiplicativity
                        //If not, we just have to perform the computations from trace form
                        if (!gequal1(gel(traceform,1)))
                        {
                            gel(traceform, nmoverr2) = wt2trivialTraceByPsi(sqrts, nmoverr2, psi, 0);
                        }
                        else
                        {
                            GEN nfactors = myfactoru(nmoverr2);
                            if(lg(gel(nfactors,1))>2)
                            {
                                gel(traceform, nmoverr2) = gmul(gel(traceform, gel(nfactors,3)[1]), gel(traceform, nmoverr2/gel(nfactors, 3)[1]));
                            }
                            /*else if (gel(nfactors,2)[1]>1)
                            {

                                gel(traceform, nmoverr2) = wt2trivialTraceByPsi(sqrts, nmoverr2, psi, 0);

                                //This is the weight 1 version! replace with weight 2 relation
                                //pari_printf("computing n=%ld with factors=%Ps", n, nfactors);
                                //gel(traceform, n) = gsub(gmul(gel(traceform, gel(nfactors,1)[1]), gel(traceform, n/gel(nfactors,1)[1])), gel(traceform, n/gel(nfactors,1)[1]/gel(nfactors,1)[1]));
                                //pari_printf("traceform is now %Ps\n", traceform);
                            }*/
                            else
                            {
                                //pari_printf("computing trace for %ld\n", nmoverr2);
                                gel(traceform, nmoverr2) = wt2trivialTraceByPsi(sqrts, nmoverr2, psi, 0);
                            }
                        }
                    }
                }
            }
        }
        gel(minspace,2) = gerepilecopy(beforeTraceComputations, traceform);
        gel(spaces, spacei) = minspace;
        //pari_printf("successfully updated space %ld of %ld\n", spacei, lg(spaces)-1);
    }
    return gerepilecopy(ltop, spaces);
}

//sigma0 used to define Eisenstein series
long
sigma0(GEN chiVals, long n, long fieldp)
{
    pari_sp ltop = avma;
    long val = 0;
    long cond = lg(chiVals)-1;
    GEN divs = divisorsu(n);
    for (long i=1; i<lg(divs); i++)
    {
        long div = umodsu(divs[i],cond);
        if (ugcd(cond, div)==1)
        {
            val = Fl_add(val, chiVals[Fl_inv(div,cond)], fieldp);
        }
    }
    gerepileupto(ltop, NULL);
    return val;
}

//sigma0Q used to define Eisenstein series over Q
GEN
sigma0Q(GEN polyVals, long n)
{
    GEN val = gen_0;
    long cond = lg(polyVals)-1;
    GEN divs = divisorsu(n);
    for (long i=1; i<lg(divs); i++)
    {
        long div = umodsu(divs[i],cond);
        if (ugcd(cond, div)==1)
        {
            val = gadd(val, pol_xn(polyVals[Fl_inv(div,cond)], 0));
        }
    }
    return val;
}

//Compute the Eisenstein constant for a given character and field
long eisConst(GEN chiVals, long fieldp)
{
    long eisC = 0;
    long cond = lg(chiVals)-1;
    for (long r=1; r<cond; r++)
    {
        if (ugcd(cond,r)==1)
        {
            eisC = Fl_sub(eisC, Fl_mul(chiVals[Fl_inv(r,cond)], r, fieldp), fieldp);
        }
    }
    eisC = Fl_div(eisC, umodsu(2*cond,fieldp), fieldp);
    return eisC;
}

//Given a character, nmax number of coeffs, fieldp giving characteristic, and constant eisC
//Return the Eisenstein series attached to infinity, unlifted
GEN eisSeries(GEN chiVals, long nmax, long fieldp, long eisC)
{
    GEN series = const_vecsmall(nmax, 0);
    series[1] = eisC;
    for (long n = 1; n<nmax; n++)
    {
        series[n+1] = sigma0(chiVals, n, fieldp);
    }
    return series;
}

//Return the Eisenstein series attached to infinity, unlifted, over Q
GEN eisSeriesQ(GEN polyVals, long nmax)
{
    GEN series = cgetg(nmax+1,t_VEC);
    gel(series,1) = gen_0;
    long cond = lg(polyVals)-1;
    for (long r=1; r<cond; r++)
    {
        if (ugcd(cond,r)==1)
        {
            GEN chirbar = pol_xn(polyVals[Fl_inv(r,cond)], 0);
            gel(series,1) = gsub(gel(series,1), gmulgs(chirbar, r));
        }
    }


    for (long n = 1; n<nmax; n++)
    {
        gel(series,n+1) = gmulgs(sigma0Q(polyVals, n), cond<<1);
    }
    return series;
}

//Given an Eisenstein series attached to infinity, and greater nmax, compute coefficients
//up to nmax
GEN extendEisSeries(GEN series, GEN chiVals, long nmax, long fieldp)
{
    pari_sp ltop = avma;
    long oldLength = lg(series)-1;
    series = shallowconcat(series, const_vecsmall(nmax-oldLength,0));
    for (long n = oldLength; n<nmax; n++)
    {
        series[n+1] = sigma0(chiVals, n, fieldp);
    }
    return gerepileupto(ltop, series);
}

//Given a matrix of basis elements and the inverse of an Eisenstein series
//divide the matrix by the series, working over fieldp
GEN multiplyMatByEis(GEN mat, GEN eis, long fieldp)
{
    long j, l = lg(mat), r = nbrows(mat);
    GEN M = cgetg(l, t_MAT);
    for (j = 1; j < l; j++)
    {
        gel(M,j) = Flx_to_Flv(Flxn_mul(Flv_to_Flx(gel(mat,j), 0), eis, r, fieldp), r);
    }
    return M;
}

//Given wt 2 space in single-variable polynomial form, a fieldp and primp a primitive fieldp-1 root
//of unity, embed the space into the field.
GEN embedWt2Space(GEN space, long fieldp, long primp)
{
    pari_sp ltop = avma;
    GEN coeffs = ZM_to_Flm(space, fieldp);
    return gerepilecopy(ltop, coeffs);
}

//Given an embedded basis, and an Eisenstein series, divide the basis by the series, working
//over the fieldp.
GEN divideBasisByEis(GEN embedBas, GEN series, long fieldp)
{
    pari_sp ltop = avma;
    GEN invEis = Flv_to_Flx(series, 0);
    invEis = Flxn_inv(invEis, lg(series),fieldp);
    GEN result = multiplyMatByEis(embedBas, invEis, fieldp);
    return gerepileupto(ltop, result);
}

//Find the maximal stable subspace for the m-th Hecke operator over fieldp
GEN MaximalTnStableSubspace(GEN gcds, GEN chiVals, GEN basis, long m, long fieldp)
{
    pari_sp ltop = avma;
    GEN smallBasis, TmBasis;
    long smallnrow = (lg(gel(basis,1))-1)/m;
    long chip = 0;
    if(myugcd(gcds, m)==1)
    {
        chip = chiVals[umodsu(m,lg(chiVals)-1)];
    }
    //Initialise a truncated version of the space
    smallBasis = rowslice(basis, 1, smallnrow);
    //TmBasis is truncated to the same level
    TmBasis = cgetg(lg(basis), t_MAT);
    for (long i = 1; i<lg(basis); i++)
    {
        GEN basisElt = const_vecsmall(smallnrow, 0);
        for (long n=1; n<=smallnrow; n++)
        {
            if (!umodsu(n,m))
            {
                basisElt[n] = Fl_add(gel(basis,i)[m*n], Fl_mul(gel(basis,i)[n/m], chip, fieldp), fieldp);
            }
            else
            {
                basisElt[n] = gel(basis,i)[m*n];
            }
        }
        gel(TmBasis, i) = basisElt;
    }

    //Repeatedly compute the Tm stable subspace by computing the kernel of these two
    //objects concatenated
    while(1)
    {
        GEN kernel = Flm_ker(concat(TmBasis, smallBasis), fieldp);
        //If the kernel is everything, the space is stable
        if (lg(kernel)==lg(basis)) return gerepileupto(ltop, basis);
        //If the kernel is 0, the stable subspace is also 0
        if (lg(kernel)==1) return gerepileupto(ltop, kernel);
        kernel = rowslice(kernel, 1, lg(basis));
        basis = Flm_mul(basis, kernel, fieldp);
        smallBasis = rowslice(basis, 1, smallnrow);
        TmBasis = Flm_mul(TmBasis, kernel, fieldp);
    }

}

//Given a level N and conrey logarithm stats, return all lower levels and conrey logarithms
//which lift to this level and character.
GEN
getLowerLevelStats(long N, GEN stats)
{
    GEN primChar = znchartoprimitive(znstar0(stoi(N),1), stats);
    long lowerLev = itos(gel(gel(gel(primChar,1),1),1));
    GEN divs = divisorsu(N/lowerLev);
    GEN lowerLevelStats = cgetg(1,t_VEC);
    for(long i = 1; i<lg(divs)-1; i++)
    {
        GEN liftLev = stoi(lowerLev*divs[i]);
        GEN liftStats = zncharinduce(gel(primChar,1), gel(primChar,2), liftLev);
        lowerLevelStats = vec_append(lowerLevelStats, mkvec2(liftLev, liftStats));
    }
    return lowerLevelStats;
}

//Find a "canonical" conrey logarithm for a given group and conrey vector. Calling this function
//ensures that we never miss a space due to Galois conjugacy
GEN bestRep(GEN group, GEN convec)
{
    pari_sp ltop = avma;
    GEN order = zncharorder(group, convec);
    GEN possMults = coprimes_zv(itos(order));
    long chiExp = itos(znconreyexp(group, convec));
    long N = itos(gel(gel(group,1),1));
    GEN best = znconreylog(group, stoi(chiExp));
    for(long i = 2; i<lg(possMults); i++)
    {
        if(possMults[i])
        {

            GEN altLog = znconreylog(group, stoi(Fl_powu(chiExp, i, N)));
            long better = 1;
            for(long j = 1; j<lg(altLog); j++)
            {
                if(itos(gel(altLog, j))>itos(gel(best, j)))
                {
                    better = 0;
                    break;
                }
                else if (itos(gel(altLog, j))<itos(gel(best, j))) break;
            }
            if (better)
            {
                best = gcopy(altLog);
            }
        }
    }
    return gerepileupto(ltop, best);
}

GEN admissiblePairs(long N, GEN stats)
{
    pari_sp ltop = avma;
    GEN factors = myfactoru(N);
    GEN pairs = mkvec(mkvec2(stoi(N), zerocol(lg(stats)-1)));
    GEN option;
    long l = lg(gel(factors,1));
    long start = 1;
    long statNum = 0;
    //If the level is even, the twist cases are a little different
    if (gel(factors,1)[1]==2)
    {
        long e = gel(factors,2)[1];
        //If the power of 2 is even
        if(e==1)
        {
            statNum--;
        }
        else if(e>2)
        {
            statNum++;
        }
        start++;
    }
    //For all other odd primes, we add the relevant twists
    for (long i = start; i<l; i++)
    {
        long e = gel(factors,2)[i];

        if (!odd(e) && !umodiu(gel(stats,statNum+i), gel(factors,1)[i]))
        {
            GEN currentOptions = gcopy(pairs);
            //Add full conductor twist
            if(e>2 || gel(factors,1)[i]!=3)
            {
                for (long j = 1; j<lg(currentOptions); j++)
                {
                    option = gcopy(gel(currentOptions, j));
                    gel(gel(option,2),statNum+i) = powuu(gel(factors,1)[i], e>>1);
                    gel(option,1) = gdiv(gel(option,1), gel(gel(option,2),statNum+i));
                    pairs = vec_append(pairs, option);
                }
            }
            if (e==2 && gequal0(gel(stats,statNum+i)))
            {
                for (long j = 1; j<lg(currentOptions); j++)
                {
                    //Add quadratic twist from e=0 and e=1
                    option = gcopy(gel(currentOptions, j));
                    gel(gel(option,2),statNum+i) = stoi(gel(factors,1)[i]*(gel(factors,1)[i]-1)>>1);
                    gel(option,1) = gdivgs(gel(option,1), gel(factors,1)[i]);
                    pairs = vec_append(pairs, option);
                    option = gcopy(option);
                    gel(option,1) = gdivgs(gel(option,1), gel(factors,1)[i]);
                    pairs = vec_append(pairs, option);
                }
            }
        }
    }
    return gerepilecopy(ltop, pairs);
}

//Is a given level and conrey log stats twist minimal
long isTwistMinimal(long N, GEN stats)
{
    pari_sp ltop = avma;
    GEN group = znstar0(stoi(N),1);
    GEN fchi = zncharconductor(group, stats);
    GEN factors=myfactoru(N);
    for(long i = 1; i<lg(gel(factors,1)); i++)
    {
        if(gel(factors,2)[i]==1) continue;
        if(gel(factors,1)[i]!=2)
        {
            long fchip = Z_lval(fchi,gel(factors,1)[i]);
            if(fchip==0 || fchip==gel(factors,2)[i]) continue;
            if(fchip>1)
            {
                set_avma(ltop);
                return 0;
            }
            GEN chiQ = znchardecompose(group, stats, stoi(gel(factors,1)[i]));
            long max2pow = gel(myfactoru(gel(factors,1)[i]-1),3)[1];
            if(itos(zncharorder(group, chiQ)) != max2pow)
            {
                set_avma(ltop);
                return 0;
            }
        }
        else
        {
            continue;
            if(gel(factors,2)[i]<3) continue;
            long fchip = Z_lval(fchi,2);
            /*if(fchip>gel(factors,2)[i]/2 && fchip<gel(factors,2)[i]){
                set_avma(ltop);
                return 0;
            }*/
            if(fchip>2 && fchip<gel(factors,2)[i]/2)
            {
                set_avma(ltop);
                return 0;
            }
        }
    }
    set_avma(ltop);
    return 1;
}



GEN getMinimalEquiv(long N, GEN stats)
{
    if (isTwistMinimal(N, stats)) return stats;
    GEN factors = myfactoru(N);
    GEN P = gel(factors,1);
    GEN E = gel(factors,2);
    GEN minStats = gcopy(stats);
    long start = 1;
    long offset = 0;
    if(!odd(N))
    {
        start++;
        if(N&3)
        {
            offset--;
        }
        else if(!(N&7))
        {
            offset++;
        }
    }
    for(long i = start; i<lg(P); i++)
    {
        if(gequal0(gel(stats,i+offset))) continue;
        if(odd(E[i])) continue;
        if(umodiu(gel(stats,i+offset), P[i])) continue;
        if(!odd(itos(gel(stats,i+offset))))
        {
            gel(minStats,i+offset)=gen_0;
        }
        else
        {
            gel(minStats,i+offset)=stoi(gel(factors,3)[i]*(P[i]-1)/P[i]);
            gel(minStats, i+offset) = gshift(gel(minStats, i+offset), -Z_lval(gel(minStats,i+offset),2));
        }
    }
    GEN group = znstar0(stoi(N), 1);
    return bestRep(group, znconreychar(group,minStats));
}

//Get a list of all character stats which we need to compute for the level N
//Currently, this is just everything, but I will restrict to only twist-minimal characters
//and only characters which can give rise to exotic representations.
GEN getAllCharStats(long N)
{
    pari_sp ltop = avma;
    GEN group = znstar0(stoi(N), 1);
    GEN allChars = chargalois(group, NULL);
    pari_sp lbot = avma;
    GEN requiredStats = cgetg(1, t_VEC);
    for(long i = 1; i<lg(allChars); i++)
    {
        //if(isTwistMinimal(N, gel(allChars,i))){
        requiredStats = vec_append(requiredStats, bestRep(group, gel(allChars, i)));
        //}
    }
    return gerepile(ltop, lbot, requiredStats);
}



//Get a list of all character stats which we need to compute for the level N
//Currently, this is just everything, but I will restrict to only twist-minimal characters
//and only characters which can give rise to exotic representations.
GEN getAltCharStats(long N)
{
    pari_sp ltop = avma;
    GEN group = znstar0(stoi(N), 1);
    GEN allChars = chargalois(group, NULL);
    pari_sp lbot = avma;
    GEN requiredStats = cgetg(1, t_VEC);
    for(long i = 1; i<lg(allChars); i++)
    {
        if(zncharisodd(group, gel(allChars,i)))
        {
            requiredStats = vec_append(requiredStats, bestRep(group, gel(allChars, i)));
        }
    }
    return gerepile(ltop, lbot, requiredStats);
}

//Get the coefficients of a weight 2 newspapce, between firstCoef and lastCoef, in matrix form
GEN getWt2newspace(long N, GEN spaces, long firstCoef, long lastCoef)
{
    GEN basis = cgetg(1,t_MAT);
    GEN allgroups = getAllGroups(N);
    GEN sqrts = mksqr(N);
    for (long i = 1; i<lg(spaces)-1; i++)
    {
        TwistChar psi = initialiseWt2TwistChar(N, gel(gel(spaces,i),1), allgroups);
        psi.gcds = mkgcd(N);
        basis = shallowconcat(basis, getBasisFromTrace(psi, sqrts, gel(spaces, i), firstCoef, lastCoef));
    }
    return basis;
}

long coefsKnownSpecific(GEN wt2data)
{
    long numKnown = 0;
    for(long j = 1; j<lg(wt2data)-1; j++)
    {
        GEN psiSpace = gel(wt2data, j);
        for(long h = 1; h<lg(gel(psiSpace,3)); h++)
        {
            GEN embed = gel(gel(psiSpace,3),h);
            long thisKnown = (lg(gel(psiSpace,2))-1)/gel(embed,2)[lg(gel(embed,2))-1];
            if(numKnown==0 || thisKnown<numKnown) numKnown = thisKnown;
        }
    }
    return numKnown;
}

long numcoefsknown(GEN database, long N)
{
    long numKnown = 0;
    pari_sp ltop = avma;
    GEN divs = divisorsu(N);
    for(long i = 2; i<lg(divs); i++)
    {
        GEN wt2data = gel(database,divs[i]);
        long thisKnown = coefsKnownSpecific(wt2data);
        if(numKnown ==0 || numKnown>thisKnown) numKnown = thisKnown;
    }
    set_avma(ltop);
    return numKnown;
}

//To the weight 2 database, append coefficients up to lastCoef
void expandBasisFor(GEN database, long N, long lastCoef)
{
    GEN divs = divisorsu(N);
    for (long i = 2; i<lg(divs); i++)
    {
        pari_sp ltop = avma;
        if (divs[i]<11) continue;
        if(vecsearch(mkvecsmalln(7, 12, 13, 16, 18, 25, 28, 60), stoi(divs[i]), NULL)>0) continue;
        GEN altSpace = expandBasisUpTo(divs[i], gcopy(gel(database, divs[i])), lastCoef);
        long didAnything = !gequal(altSpace, gel(database, divs[i]));
        if (!didAnything) {
            set_avma(ltop);
            continue;
        } else {
            gel(database, divs[i]) = gerepilecopy(ltop, altSpace);
        }
        char filename[20];
        sprintf(filename, "wt2spaces/%ld.txt", divs[i]);
        char dummyfilename[20];
        sprintf(dummyfilename, "dummies2/%ld.txt", divs[i]);
        FILE *dummy_file = fopen(dummyfilename, "w");
        flock(fileno(dummy_file), LOCK_EX);
        FILE *out_file = fopen(filename, "w");
        pari_fprintf(out_file, "%Ps\n", gel(database,divs[i]));
        fclose(out_file);
        flock(fileno(dummy_file), LOCK_UN);
        fclose(dummy_file);
    }
}

//Coefficients of a weight 2 space already known, in a matrix, append coefficients to the matrix
//up to the specified lastCoef
GEN extendWt2cuspspace(GEN database, long N, GEN knowncoefs, long lastCoef)
{
    pari_sp ltop = avma;
    long offset = nbrows(knowncoefs);
    long firstCoef = offset+1;
    GEN basis = cgetg(1,t_MAT);
    GEN divs = divisorsu(N);
    for (long i = 2; i<lg(divs); i++)
    {
        long div = divs[i];
        GEN lowerLevelNewSpace = getWt2newspace(div, gel(database,div), firstCoef, lastCoef);
        if(lg(lowerLevelNewSpace)==1) continue;
        GEN liftingDivs = divisorsu(N/div);
        GEN knownPart = matslice(knowncoefs, 1, offset, lg(basis), lg(basis)-1+(lg(liftingDivs)-1)*(lg(lowerLevelNewSpace)-1));

        GEN oldSpaces = vconcat(matslice(knownPart, 1, offset, 1, lg(lowerLevelNewSpace)-1), lowerLevelNewSpace);
        long knownIndex = lg(lowerLevelNewSpace);
            for (long j = 2; j<lg(liftingDivs); j++)
            {
                long b = liftingDivs[j];
                GEN oldSpace = vconcat(matslice(knownPart, 1, offset, knownIndex, knownIndex+lg(lowerLevelNewSpace)-2), zeromatcopy(lastCoef+1-firstCoef, lg(lowerLevelNewSpace)-1));
                for(long n = (firstCoef-1)/b+1; n<=lastCoef/b; n++)
                {
                    long nb = n*b;
                    for (long m = 1; m<lg(lowerLevelNewSpace); m++)
                    {
                        gcoeff(oldSpace, nb, m) = gcoeff(oldSpaces, n, m);
                    }
                }
                oldSpaces = shallowconcat(oldSpaces, oldSpace);
                knownIndex+=lg(lowerLevelNewSpace)-1;
            }
            basis = shallowconcat(basis, oldSpaces);
    }
    return gerepilecopy(ltop, basis);
}

//Get the weight 2 cuspform space of level N in matrix form up to lastCoef
GEN getWt2cuspspace(GEN database, long N, long lastCoef)
{
    pari_sp ltop = avma;
    GEN basis = cgetg(1,t_MAT);
    GEN divs = divisorsu(N);
    for (long i = 2; i<lg(divs); i++)
    {
        long div = divs[i];
        GEN lowerLevelNewSpace = getWt2newspace(div, gel(database,div), 1, lastCoef);
        GEN liftingDivs = divisorsu(N/div);
        GEN oldSpaces = lowerLevelNewSpace;


            for (long j = 2; j<lg(liftingDivs); j++)
            {
                long b = liftingDivs[j];
                GEN oldSpace = zeromatcopy(lastCoef, lg(lowerLevelNewSpace)-1);
                for(long n = 1; n<=lastCoef/b; n++)
                {
                    long nb = n*b;
                    for (long m = 1; m<lg(lowerLevelNewSpace); m++)
                    {
                        gcoeff(oldSpace, nb, m) = gcoeff(lowerLevelNewSpace, n, m);
                    }
                }
                oldSpaces = shallowconcat(oldSpaces, oldSpace);
            }
            basis = shallowconcat(basis, oldSpaces);
    }
    return gerepilecopy(ltop, basis);
}

//Given two characters (as vecsmalls of values), and specified number of coefficients,
//give the Eisenstein series attached to those characters, over the field
GEN eisFromChars(GEN chi1, GEN chi2, long numcoefs, long fieldp)
{
    pari_sp ltop = avma;
    GEN element = cgetg(numcoefs+1, t_VECSMALL);
    for (long n = 1; n<=numcoefs; n++)
    {
        GEN divs = divisorsu(n);
        long entry = 0;
        for(long i = 1; i<lg(divs); i++)
        {
            long eval1 = chi1[umodsu(divs[i]-1,lg(chi1)-1)+1];
            long eval2 = chi2[umodsu(divs[lg(divs)-i]-1,lg(chi2)-1)+1];
            entry = Fl_add(entry,Fl_mul(eval1,eval2, fieldp), fieldp);
        }
        element[n]=entry;
    }
    return gerepileupto(ltop, element);
}

//CHANGED HERE
//CHANGED HERE

//List all pairs of chars for Eisenstein series we need to divide by
GEN eisChars(long N, GEN gcds, GEN stats)
{
    long conductor = N;
    pari_sp ltop = avma;
    GEN group = znstar0(stoi(N),1);
    GEN chiExp = Fp_inv(znconreyexp(group, stats),stoi(N));
    GEN cond1, cond2;
    long divfact, firstgcd, secondgcd;


    pari_sp lbot = avma;


    GEN chars = cgetg(1, t_VEC);

    for(long i=2; i<N; i++)
    {
        if(myugcd(gcds, i)==1)
        {
            if (!zncharisodd(group,stoi(i)))
            {
                cond1 = zncharconductor(group, stoi(i));
                cond2 = zncharconductor(group, gmodgs(sstoQ(itos(chiExp),i),N));
                if(!gequal0(gmodsg(N,gmul(cond1,cond2)))) continue;
                if(gequal0(gmodgs(cond1,conductor))||gequal0(gmodgs(cond2,conductor))) continue;
                divfact = N/conductor;
                firstgcd = ugcd(itos(ggcd(ggcd(cond1,cond2),stoi(divfact))),conductor);
                divfact /= firstgcd;
                cond1 = gdivgs(cond1,firstgcd);
                cond2 = gdivgs(cond2, firstgcd);
                secondgcd = ugcd(itos(ggcd(cond1,cond2)),divfact);
                divfact /= secondgcd*secondgcd;
                chars = vec_append(chars, mkvecsmall3(i, itos(gmodgs(sstoQ(itos(chiExp),i),N)), divfact));
            }
        }
    }
    /*pari_printf("chiexp is %Ps\n", chiExp);
    pari_printf("chars are %Ps\n", chars);*/
    return gerepile(ltop, lbot, chars);
}

GEN eisCharsAlt(long N, GEN gcds, GEN stats)
{
    pari_sp ltop = avma;
    GEN group = znstar0(stoi(N),1);
    GEN chiExp = Fp_inv(znconreyexp(group, stats),stoi(N));
    GEN cond1, cond2;
    long conductor = itos(zncharconductor(group, stats));
    long NoverNstar = N/conductor;
    pari_sp lbot = avma;


    GEN chars = cgetg(1, t_VEC);

    for(long i=2; i<N; i++)
    {
        if(myugcd(gcds, i)==1)
        {
            if (!zncharisodd(group, stoi(i)))
            {
                cond1 = zncharconductor(group, stoi(i));
                cond2 = zncharconductor(group, stoi(Fl_div(i,itos(chiExp),N)));
                if(!gequal0(gmodsg(N,gmul(cond1,cond2)))) continue;
                if(umodsu(NoverNstar, ugcd(itos(cond1), N/itos(cond1)))) continue;
                chars = vec_append(chars, mkvecsmall2(i, Fl_div(itos(chiExp),i,N)));
            }
        }
    }
    return gerepile(ltop, lbot, chars);
}


GEN eisValsFromChiStats(long N, GEN stats, long fieldp, GEN chiStats, long fieldprim)
{
    pari_sp ltop = avma;
    GEN vals = cgetg(lg(chiStats), t_VEC);
    GEN group = znstar0(stoi(N),1);
    GEN fieldorder = gsubsg(fieldp, gen_1);
    for(long i = 1; i<lg(vals); i++)
    {

        GEN chi1 = znchartoprimitive(group,stoi(gel(chiStats,i)[1]));
        GEN chi2 = znchartoprimitive(group, stoi(gel(chiStats,i)[2]));
        GEN chi1vals = cgetg(itos(gel(gel(gel(chi1,1),1),1))+1,t_VECSMALL);
        GEN chi2vals = cgetg(itos(gel(gel(gel(chi2,1),1),1))+1,t_VECSMALL);

        for (long n = 1; n<lg(chi1vals); n++)
        {
            GEN evaluation = znchareval(gel(chi1,1),gel(chi1,2), stoi(n), fieldorder);
            if (!gequalm1(evaluation))
            {
                chi1vals[n] = Fl_powu(fieldprim, itos(evaluation), fieldp);
            }
            else
            {
                chi1vals[n] = 0;
            }
        }
        for (long n = 1; n<lg(chi2vals); n++)
        {
            GEN evaluation = znchareval(gel(chi2,1),gel(chi2,2), stoi(n), fieldorder);
            if (!gequalm1(evaluation))
            {
                chi2vals[n] = Fl_powu(fieldprim, itos(evaluation), fieldp);
            }
            else
            {
                chi2vals[n] = 0;
            }
        }
        gel(vals,i) = mkvec2(chi1vals, chi2vals);
    }
    return gerepilecopy(ltop, vals);
}

//Given stats including the conrey label of two characters and the greatest possible lift,
//returns the Eisenstein series attached to those characters, lifted by that amount
GEN eisFromChiVals(long fieldp, long numcoefs, GEN chiStats, long div)
{
    pari_sp ltop = avma;
    GEN chi1vals = gel(chiStats,1);
    GEN chi2vals = gel(chiStats,2);
    GEN baseEis = eisFromChars(chi1vals, chi2vals, numcoefs/div, fieldp);
    pari_sp lbot = avma;
    GEN lift = const_vecsmall(numcoefs, 0);
    for (long n = 1; n<=numcoefs/div; n++)
    {
        lift[n*div] = baseEis[n];
    }
    lift = vecslice(lift, div, numcoefs);
    return gerepile(ltop, lbot, lift);

}

//Given the master polynomial version of a weight 2 space, return the dimension of this space
long getSpaceDim(GEN space)
{
    pari_sp ltop = avma;
    long dim = 0;
    for (long i = 1; i<lg(space); i++)
    {
        GEN twistSpace = gel(space, i);
        long dimOfSpace = lg(twistSpace)-1;
        dim += dimOfSpace;
    }
    set_avma(ltop);
    return dim;
}

//Get the subspace of the weight-2 trivial character space which has the specified number of zeros.
GEN getCuspidalUpTo(GEN basis, long numzeros, long fieldp)
{
    GEN cuspidalBasis = gcopy(basis);
    for(long i = 1; i<=numzeros; i++)
    {
        long j = 1;
        for(; j<lg(cuspidalBasis); j++)
        {
            if (gel(cuspidalBasis,j)[i])
            {
                break;
            }
        }
        if (j==lg(cuspidalBasis)) continue;
        GEN pivotVec = Flv_Fl_div(gel(cuspidalBasis,j), gel(cuspidalBasis,j)[i], fieldp);
        long counter = 1;
        for(long k = 1; k<lg(cuspidalBasis); k++)
        {
            if (k==j) continue;
            gel(cuspidalBasis, counter) = Flv_sub(gel(cuspidalBasis, k), Flv_Fl_mul(pivotVec, gel(cuspidalBasis,k)[i],fieldp),fieldp);
            counter++;
        }
        cuspidalBasis = matslice(cuspidalBasis, 1, nbrows(cuspidalBasis), 1, lg(cuspidalBasis)-2);
    }
    return cuspidalBasis;
}

//Find the hecke-stable subspace, stable up to the specified hecke operator T_p
GEN stabiliseUpTo(GEN gcds, GEN chiVals, GEN dividedSpace, long heckep, long fieldp, long oldDim)
{
    pari_sp ltop = avma;
    long Tp = 2;

    GEN stable = MaximalTnStableSubspace(gcds, chiVals, dividedSpace, Tp, fieldp);
    stable = gerepilecopy(ltop, stable);
    if (lg(stable)==oldDim+1) return stable;

    while (heckep != Tp)
    {
        Tp = unextprime(Tp+1);
        stable = MaximalTnStableSubspace(gcds, chiVals, stable, Tp, fieldp);
        stable = gerepilecopy(ltop, stable);
        if (lg(stable)==oldDim+1) return stable;
    }
    return gerepileupto(ltop, stable);
}

//Diagonalise the weight 1 space
GEN diagonalise(GEN gcds, GEN chiVals, long oldDim, GEN space, long fieldp)
{
    pari_sp ltop = avma;
    if(lg(space)==2)
    {
        return Flm_Fl_mul(space, Fl_inv(gel(space,1)[1],fieldp), fieldp);
    }

    GEN TmBasis = cgetg(lg(space), t_MAT);
    long p = 2;

    long smallnrow = (lg(gel(space,1))-1)/p;
    long chip = 0;
    if(myugcd(gcds,p)==1)
    {
        chip = chiVals[umodsu(p,lg(chiVals)-1)];
    }
    GEN smallBasis = rowslice(space, 1, smallnrow);
    GEN mapsTo = cgetg(lg(space), t_MAT);
    for (long i = 1; i<lg(space); i++)
    {
        gel(TmBasis,i) = const_vecsmall(smallnrow, 0);
        gel(mapsTo,i) = const_vecsmall(smallnrow, 0);
        for (long n=1; n<=smallnrow; n++)
        {
            gel(TmBasis,i)[n] = gel(space,i)[p*n];
            if (!umodsu(n,p))
            {
                gel(TmBasis,i)[n] = Fl_add(gel(TmBasis,i)[n], Fl_mul(gel(space,i)[n/p], chip, fieldp), fieldp);
            }
        }
    }

    GEN actsNew, actsLike, factors, oldRoots, fullRoots, newRoots;

    while(1)
    {
        long randi = random_Fl(fieldp-10)+10;

        mapsTo = Flm_add(mapsTo, Flm_Fl_mul(TmBasis, randi,fieldp), fieldp);

        actsLike = Flm_gauss(smallBasis, mapsTo, fieldp);
        actsNew = matslice(actsLike, oldDim+1, lg(actsLike)-1, oldDim+1, lg(actsLike)-1);

        factors = Flx_factor(Flm_charpoly(actsNew, fieldp), fieldp);

        long hasRepeats = 0;

        for (long i = 1; i<=nbrows(factors); i++)
        {
            /*if (lg(gcoeff(factors, i, 1))>4)
            {
                pari_printf("actsNew is %Ps\n", actsNew);
                pari_printf("heckep is %ld\n", p);
                pari_printf("randi is %ld\n", randi);
                //Tm doesn't split. Need a different field.
                pari_printf("factors are %Ps\n", factors);
                pari_printf("roots are %Ps\n", Flx_roots(Flm_charpoly(actsNew, fieldp), fieldp));
                pari_printf("oneroot is %ld\n", Flx_oneroot_split(gcoeff(factors,i,1), fieldp));
                set_avma(ltop);
                return NULL;
            }*/
            if(gel(factors,2)[i]!=1)
            {
                hasRepeats = 1;
            }
        }

        if (!hasRepeats)
        {
            newRoots=Flx_roots(Flm_charpoly(actsNew, fieldp), fieldp);
            if(!oldDim) break;
            oldRoots=Flx_roots(Flm_charpoly(matslice(actsLike, 1, oldDim, 1, oldDim), fieldp), fieldp);
            fullRoots=Flx_roots(Flm_charpoly(actsLike, fieldp), fieldp);
            if(lg(newRoots)+lg(oldRoots)-1==lg(fullRoots)) break;
        }

        p = unextprime(p+1);
        smallnrow = (lg(gel(space,1))-1)/p;
        smallBasis = rowslice(space, 1, smallnrow);
        if(Flm_rank(smallBasis, fieldp)<lg(smallBasis)-1)
        {
            set_avma(ltop);
            return stoi(-p);
        }
        if (myugcd(gcds,p)==1)
        {
            chip = chiVals[umodsu(p,lg(chiVals)-1)];
        }
        else
        {
            chip = 0;
        }
        mapsTo = rowslice(mapsTo, 1, smallnrow);

        for (long i = 1; i<lg(space); i++)
        {
            gel(TmBasis,i) = const_vecsmall(smallnrow, 0);
            for (long n=1; n<=smallnrow; n++)
            {
                gel(TmBasis,i)[n] = gel(space,i)[p*n];
                if (!umodsu(n,p))
                {
                    gel(TmBasis,i)[n] = Fl_add(gel(TmBasis,i)[n], Fl_mul(gel(space,i)[n/p], chip, fieldp), fieldp);
                }
            }
        }
    }

    GEN H = cgetg(1, t_MAT);
    for (long i = 1; i<lg(newRoots); i++)
    {
        GEN eigMat = matid_Flm(lg(actsNew)-1);
        eigMat = Flm_Fl_mul(eigMat, fieldp-newRoots[i], fieldp);
        GEN I = Flm_add(actsNew, eigMat, fieldp);
        H = concat(H, Flm_ker(I, fieldp));
    }

    GEN eigenBasis = Flm_mul(vecslice(space, oldDim+1, lg(space)-1), H, fieldp);

    actsLike = gconcat(matslice(actsLike,1,oldDim,1,oldDim), Flm_mul(matslice(actsLike,1,oldDim,oldDim+1,lg(actsLike)-1),H,fieldp));

    if(oldDim>0)
    {
        for(long i = 1; i<lg(eigenBasis); i++)
        {
            GEN orthogonaliser = scalar_Flm(fieldp-newRoots[i],oldDim);
            orthogonaliser = Flm_add(orthogonaliser, matslice(actsLike, 1, oldDim, 1, oldDim), fieldp);
            orthogonaliser = Flm_inv(orthogonaliser, fieldp);
            orthogonaliser = Flm_Flc_mul(orthogonaliser, gel(actsLike, i+oldDim), fieldp);
            gel(eigenBasis,i)=Flv_sub(gel(eigenBasis,i), Flm_Flc_mul(matslice(space, 1,nbrows(space),1,oldDim), orthogonaliser, fieldp), fieldp);
        }
    }




    for (long i=1; i<lg(eigenBasis); i++)
    {
        for (long j = 1; j<=nbrows(eigenBasis); j++)
        {
            if (gel(eigenBasis,i)[j])
            {
                gel(eigenBasis, i) = Flv_Fl_div(gel(eigenBasis, i), gel(eigenBasis,i)[j], fieldp);
                break;
            }
        }
    }

    return gerepilecopy(ltop,eigenBasis);

}

//BasisToSatake
GEN basisToSatake(GEN gcds, long N, GEN basis, GEN chiVals, long fieldp, long primforp)
{
    long length = 1;
    while(uprime(length)<=nbrows(basis)) length++;
    GEN satakes = cgetg(1, t_MAT);
    for(long i = 1; i<lg(basis); )
    {
        GEN satakeVec = cgetg(length+1, t_VECSMALL);
        satakeVec[1] = 1;
        for(long j=1; j<length; j++)
        {
            long p = uprime(j);
            if(myugcd(gcds, p)==1)
            {
                GEN satakePol = const_vecsmall(4, 0);
                satakePol[2] = chiVals[umodsu(p,lg(chiVals)-1)];
                satakePol[3] = umodsu(-gel(basis,i)[p],fieldp);
                satakePol[4] = 1;
                GEN roots = Flx_roots(satakePol, fieldp);
                if(lg(roots)==1)
                {
                    //Characteristic polynomial doesn't split over the field!
                    //This means the form must be ethereal - we cannot generate Satake parameters for it
                    goto OUTERLOOP;
                }
                satakeVec[j+1] = Fl_log(roots[1], primforp, fieldp-1, fieldp);
                long satakeDenominator = (fieldp-1)/ugcd(satakeVec[j+1], fieldp-1);
                if(umodsu(satakeVec[1], satakeDenominator))
                {
                    long newcommon = ulcm(satakeDenominator, satakeVec[1])/satakeVec[1];
                    for(long h = 1; h<=j; h++)
                    {
                        if(satakeVec[h]>0) satakeVec[h]*=newcommon;
                    }
                }
                satakeVec[j+1]*=satakeVec[1];
                satakeVec[j+1]/=fieldp-1;
            }
            else
            {
                if(gel(basis,i)[p])
                {
                    satakeVec[j+1] = Fl_log(gel(basis,i)[p], primforp, fieldp-1, fieldp);
                    long satakeDenominator = (fieldp-1)/ugcd(satakeVec[j+1], fieldp-1);
                    if(umodsu(satakeVec[1], satakeDenominator))
                    {
                        long newcommon = ulcm(satakeDenominator, satakeVec[1])/satakeVec[1];
                        for(long h = 1; h<=j; h++)
                        {
                            if(satakeVec[h]>0) satakeVec[h]*=newcommon;
                        }
                    }
                    satakeVec[j+1]*=satakeVec[1];
                    satakeVec[j+1]/=fieldp-1;
                }
                else
                {
                    satakeVec[j+1]=-1;
                }
            }
        }
        satakes = vec_append(satakes, satakeVec);
OUTERLOOP:
        i++;
    }
    return satakes;
}

GEN satakesToZetas(long N, GEN satakes, GEN xqPowers, long coeffsneeded)
{
    long basePower = (lg(xqPowers)-1)/satakes[1];
    long vecLength = 1;
    while(uprime(vecLength)<=coeffsneeded) vecLength++;
    GEN zetas = cgetg(vecLength, t_VEC);
    for (long i = 1; i<vecLength; i++)
    {
        if (satakes[i+1]==-1)
        {
            gel(zetas,i)=gen_0;
        }
        else
        {
            gel(zetas,i)=gel(xqPowers, basePower*satakes[i+1]+1);
        }
    }
    return zetas;
}

GEN liftSatakeToFp(long M, GEN satakes, GEN embedVals, long fieldp, long primp)
{
    GEN coefs = cgetg(uprime(lg(satakes)-2), t_VECSMALL);
    coefs[1] = 1;
    long satakePrim = Fl_powu(primp, (fieldp-1)/satakes[1], fieldp);
    for (long j = 1; uprime(j)<lg(coefs); j++)
    {
        long p = uprime(j);
        if (umodsu(M, p))
        {
            long firstPart = Fl_powu(satakePrim, satakes[j+1], fieldp);
            long secondPart = embedVals[umodsu(p, lg(embedVals)-1)];
            secondPart = Fl_div(secondPart, firstPart, fieldp);
            coefs[p] = Fl_add(firstPart, secondPart, fieldp);
        }
        else
        {
            if (satakes[j+1]==-1)
            {
                coefs[p] = 0;
            }
            else
            {
                coefs[p] = Fl_powu(satakePrim, satakes[j+1], fieldp);
            }
        }
    }

    for (long n = 4; n<lg(coefs); n++)
    {
        if(!uisprime(n))
        {
            GEN nfactors = myfactoru(n);
            if(nbrows(nfactors)>1)
            {
                long n1 = gel(nfactors,3)[1];
                long n2 = n/n1;
                coefs[n] = Fl_mul(coefs[n1],coefs[n2],fieldp);
            }
            else
            {
                long p = gel(nfactors,1)[1];
                if(umodsu(M,p))
                {
                    long chip = embedVals[umodsu(p,lg(embedVals)-1)];
                    coefs[n] = Fl_sub(Fl_mul(coefs[p], coefs[n/p], fieldp), Fl_mul(chip, coefs[n/p/p], fieldp), fieldp);
                }
                else
                {
                    coefs[n]=Fl_mul(coefs[p],coefs[n/p],fieldp);
                }
            }
        }
    }
    return(coefs);
}

GEN liftSatakeToQ(long M, GEN satakes, GEN polyVals, long numcoefs, long definedOver, long charOrder)
{
    GEN poldef = polcyclo(definedOver, 0);
    GEN coefs = cgetg(numcoefs+1, t_VEC);
    gel(coefs,1) = pol_1(0);
    long satakemult = definedOver/satakes[1];
    long charmult = definedOver/charOrder;

    for (long j = 1; uprime(j)<=numcoefs; j++)
    {
        long p = uprime(j);
        if (umodsu(M, p))
        {
            long firstExponent = umodsu(satakes[j+1]*satakemult,definedOver);
            long secondExponent = umodsu(charmult*polyVals[umodsu(p, lg(polyVals)-1)], definedOver);
            secondExponent = Fl_sub(secondExponent, firstExponent, definedOver);
            gel(coefs,p) = gadd(ZX_rem(pol_xn(firstExponent,0),poldef), ZX_rem(pol_xn(secondExponent, 0),poldef));
        }
        else
        {
            if (satakes[j+1]==-1)
            {
                gel(coefs,p) = gen_0;
            }
            else
            {
                gel(coefs,p) = ZX_rem(pol_xn(umodsu(satakes[j+1]*satakemult,definedOver), 0),poldef);
            }
        }
    }

    for (long n = 4; n<=numcoefs; n++)
    {
        if(!uisprime(n))
        {
            GEN nfactors = myfactoru(n);
            if(nbrows(nfactors)>1)
            {
                long n1 = gel(nfactors,3)[1];
                long n2 = n/n1;
                gel(coefs,n) = ZXQ_mul(gel(coefs,n1),gel(coefs,n2), poldef);
            }
            else
            {
                long p = gel(nfactors,1)[1];
                if(umodsu(M,p))
                {
                    GEN chip = ZX_rem(pol_xn(charmult*polyVals[umodsu(p,lg(polyVals)-1)], 0),poldef);
                    gel(coefs,n)= gsub(ZXQ_mul(gel(coefs,p),gel(coefs,n/p), poldef),ZXQ_mul(chip,gel(coefs,n/p/p), poldef));
                }
                else
                {
                    gel(coefs,n)=ZXQ_mul(gel(coefs,p),gel(coefs,n/p), poldef);
                }
            }
        }
    }
    return(coefs);
}

GEN getKnownForms(GEN chiVals, GEN database, long N, GEN stats, GEN wt1data, long fieldp, long primforp, long numCoeffs, GEN eis, GEN stable)
{
    GEN knownForms = cgetg(1,t_MAT);
    GEN lowerLevelStats = getLowerLevelStats(N, stats);
    for (long i = 1; i<lg(lowerLevelStats); i++)
    {
        long div = itos(gel(gel(lowerLevelStats, i), 1));
        GEN oldData = gel(wt1data, div);
        if (gequal0(oldData)) continue;
        for (long j = 1; j<lg(oldData); j++)
        {
            if (gequal(gel(gel(oldData, j), 1), gel(gel(lowerLevelStats, i), 2)))
            {
                GEN satakes = gel(gel(oldData,j), 2);
                GEN satakesToForms = cgetg(1,t_MAT);
                for(long satakei = 1; satakei<lg(satakes); satakei++){
                    satakesToForms = vec_append(satakesToForms, liftSatakeToFp(div, vec_to_vecsmall(gel(satakes,satakei)), chiVals, fieldp, primforp));
                }
                long shorterLength = nbrows(satakesToForms);
                if(shorterLength>nbrows(stable)) shorterLength = nbrows(stable);
                GEN truncatedSpace;
                if(Flm_rank(rowslice(stable,1,shorterLength), fieldp)<lg(stable)-1){
                    GEN wt2space = getWt2cuspspace(database, div, numCoeffs);
                    GEN tempEmbed = embedWt2Space(wt2space, fieldp, primforp);
                    GEN tempWt1 = divideBasisByEis(tempEmbed, eis, fieldp);
                    GEN gaussTransform = Flm_gauss(rowslice(tempWt1,1,shorterLength), satakesToForms, fieldp);
                    truncatedSpace = Flm_mul(tempWt1, gaussTransform, fieldp);
                } else {
                GEN gaussTransform = Flm_gauss(rowslice(stable,1,shorterLength), rowslice(satakesToForms,1,shorterLength), fieldp);
                truncatedSpace = Flm_mul(stable, gaussTransform, fieldp);
                }
                GEN liftDivs = divisorsu(N/div);
                if(nbrows(truncatedSpace)>nbrows(satakesToForms)){
                    GEN newSatakes = basisToSatake(mkgcd(div), div, truncatedSpace, chiVals, fieldp, primforp);
                    gel(gel(oldData,j),2) = newSatakes;
                    char filename[20];
                    char dummyfilename[20];
                    sprintf(filename, "wt1spaces/%ld.txt", div);
                    sprintf(dummyfilename, "dummies1/%ld.txt", div);
                    FILE *dummy_file = fopen(dummyfilename, "w");
                    flock(fileno(dummy_file), LOCK_EX);
                    FILE *out_file = fopen(filename, "w");
                    pari_fprintf(out_file, "%Ps\n", oldData);
                    fclose(out_file);
                    flock(fileno(dummy_file), LOCK_UN);
                    fclose(dummy_file);
                }
                for(long h = 1; h<lg(truncatedSpace); h++)
                {
                    GEN baseForm = gel(truncatedSpace, h);
                    knownForms = vec_append(knownForms, baseForm);
                    for (long divi=2; divi<lg(liftDivs); divi++)
                    {
                        GEN liftedForm = const_vecsmall(numCoeffs, 0);
                        for(long coef = 1; coef<numCoeffs/liftDivs[divi]+1; coef++)
                        {
                            liftedForm[coef*liftDivs[divi]]=baseForm[coef];
                        }
                        knownForms = vec_append(knownForms, liftedForm);
                    }
                }

            }
        }
    }
    return knownForms;
}

long getOldLCM(long N, GEN stats, GEN wt1data)
{
    long h = 1;
    GEN lowerLevelStats = getLowerLevelStats(N, stats);
    for (long i = 1; i<lg(lowerLevelStats); i++)
    {
        long div = itos(gel(gel(lowerLevelStats, i), 1));
        GEN oldData = gel(wt1data, div);
        if (gequal0(oldData)) continue;
        for (long j = 1; j<lg(oldData); j++)
        {
            if (gequal(gel(gel(oldData, j), 1), gel(gel(lowerLevelStats, i), 2)))
            {
                for(long oldi = 1; oldi<lg(gel(gel(oldData,j), 2)); oldi++){
                    h = ulcm(h, itos(gcoeff(gel(gel(oldData,j),2),1,oldi)));
                }
            }
        }
    }
    return h;
}

long wt1newformdimension(long N, GEN stats, GEN database)
{
    //GEN minStats = getMinimalEquiv(N, stats);
    GEN oldData = gel(gel(database,1), N);
    if (!gequal0(oldData))
    {
        for (long j = 1; j<lg(oldData); j++)
        {
            if (gequal(gel(gel(oldData, j), 1), stats))
            {
                return lg(gel(gel(oldData,j),2))-1;
            }
        }
    }
    if(N>=lg(gel(database,3))) return 0;
    GEN dihedralData = gel(gel(database,3),N);
    if (gequal0(dihedralData)) return 0;
    for (long j = 1; j<lg(dihedralData); j++)
    {
        if (gequal(gel(gel(dihedralData, j), 1), stats))
        {
            return itos(gel(gel(dihedralData,j),2));
        }
    }
    return 0;
}

long wt1oldformdimension(long N, GEN stats, GEN database)
{
    pari_sp ltop = avma;
    long dimension = 0;
    GEN lowerLevelStats = getLowerLevelStats(N, stats);
    for (long i = 1; i<lg(lowerLevelStats); i++)
    {
        long div = itos(gel(gel(lowerLevelStats, i), 1));
        dimension += wt1newformdimension(div, gel(gel(lowerLevelStats,i),2), database)*itos(sumdivk(sstoQ(N,div),0));
    }
    set_avma(ltop);
    return dimension;
}

GEN getDihedralImages(long N, GEN stats, GEN database)
{
    if(N>=lg(database)) return NULL;
    GEN dihedralData = gel(database, N);
    if(gequal0(dihedralData)) return NULL;
    for(long i = 1; i<lg(dihedralData); i++)
    {
        if(gequal(gel(gel(dihedralData,i),1), stats))
        {
            return gel(gel(dihedralData,i),3);
        }
    }
    return NULL;
}


long getDihedralLCM(long N, GEN stats, GEN database)
{
    if(N>=lg(database)) return 1;
    GEN dihedralData = gel(database, N);
    if(gequal0(dihedralData)) return 1;
    for(long i = 1; i<lg(dihedralData); i++)
    {
        if(gequal(gel(gel(dihedralData,i),1), stats))
        {
    long dihedralLCM = 1;
    for(long j=1; j<lg(gel(gel(dihedralData,i),3)); j++){
        dihedralLCM = ulcm(dihedralLCM, itos(gel(gel(gel(dihedralData,i),3),j)));
    }

            return dihedralLCM;
        }
    }
    return 1;
}


long getDihedralDim(long N, GEN stats, GEN database)
{
    if(N>=lg(database)) return 0;
    GEN dihedralData = gel(database, N);
    if(gequal0(dihedralData)) return 0;
    for(long i = 1; i<lg(dihedralData); i++)
    {
        if(gequal(gel(gel(dihedralData,i),1), stats))
        {
            return itos(gel(gel(dihedralData,i),2));
        }
    }
    return 0;
}

void displayForms(GEN N, GEN chiexp, GEN database, long numcoefs)
{
    GEN group = znstar0(N,1);
    GEN chiLog = znconreychar(group, chiexp);
    chiLog = bestRep(group, chiLog);
    GEN chiPrim = znchartoprimitive(group, chiLog);
    GEN normal = znconreylog_normalize(gel(chiPrim,1), gel(chiPrim,2));
    long charOrder = itos(zncharorder(group, chiLog));
    GEN polyVals = ncharvecexpo(gel(chiPrim,1), normal);
    GEN wt1data = gel(gel(database,1),itos(N));
    if(!gequal0(wt1data))
    {
        for(long i=1; i<lg(wt1data); i++)
        {
            GEN transformationData = gel(wt1data,i);
            if(gequal(gel(transformationData,1), chiLog))
            {
                long numknown = numcoefsknown(gel(database,2),itos(N));
                if (numcoefs > numknown)
                {
                    pari_printf("%ld coefficients requested but only %ld coefficients stored. Computing more. This may take a while.\n", numcoefs, numknown);
                    expandBasisFor(gel(database,2), itos(N), numcoefs);
                }
                GEN wt2space = getWt2cuspspace(gel(database,2), itos(N), numcoefs);
                long cycloOrder = itos(gel(transformationData,2));
                GEN cycloPol = polcyclo(cycloOrder, 0);
                GEN xqPowers = RgXQ_powers(pol_x(0), cycloOrder-1, cycloPol);
                for(long i = 1; i<lg(xqPowers); i++)
                {
                    gel(xqPowers, i) = mkpolmod(gel(xqPowers, i), cycloPol);
                }
                GEN formsInWt2 = ZXQM_mul(wt2space, gel(transformationData,3), cycloPol);
                formsInWt2 = gsubst(formsInWt2, 0, gel(xqPowers,2));

                GEN embedVals = cgetg(lg(polyVals), t_VEC);
                for(long j = 1; j<lg(embedVals); j++)
                {
                    if (polyVals[j]!=-1)
                    {
                        gel(embedVals,j)=gel(xqPowers, 1+polyVals[j]*cycloOrder/charOrder);
                    }
                    else
                    {
                        gel(embedVals,j) = mkpolmod(gen_0, cycloPol);
                    }
                }
                GEN eisQ = eisSeriesQ(polyVals, numcoefs);
                eisQ = gsubst(eisQ, 0, gel(xqPowers, 1+cycloOrder/charOrder));
                eisQ = RgV_to_RgX(eisQ, 1);
                eisQ = RgXn_inv(eisQ, numcoefs);

                for(long i = 1; i<lg(formsInWt2); i++)
                {
                    GEN wt1Form = RgXn_mul(gconcat(gen_0,gel(formsInWt2,i)), eisQ, numcoefs);
                    wt1Form = RgX_to_RgC(wt1Form, numcoefs);
                    GEN fourierExpansion = lift(wt1Form);
                    long deflateBy = cycloOrder;
                    for(long j = 2; j<lg(fourierExpansion); j++)
                    {
                        if(gequal0(gel(fourierExpansion, j))) continue;
                        gel(fourierExpansion,j) = QXQ_div(gel(fourierExpansion,j), gel(fourierExpansion,1), cycloPol);
                        deflateBy = ugcd(deflateBy, degree(gel(fourierExpansion,j)));
                    }
                    gel(fourierExpansion,1) = gen_1;
                    if(deflateBy==cycloOrder)
                    {
                        pari_printf("The form is %Ps\n", fourierExpansion);
                    }
                    else if (deflateBy>1)
                    {
                        for(long j = 2; j<lg(fourierExpansion); j++)
                        {
                            gel(fourierExpansion, j) = RgX_deflate(gel(fourierExpansion,j), deflateBy);
                        }
                        pari_printf("The form is %Ps\n", fourierExpansion);
                        pari_printf("where x is a primitive %ld root of unity\n", cycloOrder/deflateBy);

                    }
                    else
                    {
                        pari_printf("The form is %Ps\n", fourierExpansion);
                        pari_printf("where x is a primitive %ld root of unity\n", cycloOrder);
                    }
                }
                return;
            }
        }
    }
}

void getFormDetails(GEN N, GEN chiexp, GEN database)
{
    pari_sp ltop = avma;
    GEN group = znstar0(N,1);
    GEN chiLog = znconreychar(group, chiexp);
    chiLog = bestRep(group, chiLog);
    long dihedralDim = getDihedralDim(itos(N), chiLog, gel(database,3));
    GEN chiPrim = znchartoprimitive(group, chiLog);
    GEN normal = znconreylog_normalize(gel(chiPrim,1), gel(chiPrim,2));
    long charOrder = itos(zncharorder(group, chiLog));
    GEN polyVals = ncharvecexpo(gel(chiPrim,1), normal);
    GEN wt1data = gel(gel(database,1),itos(N));
    if(!gequal0(wt1data))
    {
        for(long i=1; i<lg(wt1data); i++)
        {
            GEN transformationData = gel(wt1data,i);
            if(gequal(gel(transformationData,1), chiLog))
            {
                long coeffsneeded = numcoefsknown(gel(database,2),itos(N));
                GEN wt2space = getWt2cuspspace(gel(database,2), itos(N), coeffsneeded);
                long cycloOrder = itos(gel(transformationData,2));
                GEN cycloPol = polcyclo(cycloOrder, 0);
                GEN xqPowers = RgXQ_powers(pol_x(0), cycloOrder-1, cycloPol);
                for(long i = 1; i<lg(xqPowers); i++)
                {
                    gel(xqPowers, i) = mkpolmod(gel(xqPowers, i), cycloPol);
                }
                GEN formsInWt2 = ZXQM_mul(wt2space, gel(transformationData,3), cycloPol);
                formsInWt2 = gsubst(formsInWt2, 0, gel(xqPowers,2));

                GEN embedVals = cgetg(lg(polyVals), t_VEC);
                for(long j = 1; j<lg(embedVals); j++)
                {
                    if (polyVals[j]!=-1)
                    {
                        gel(embedVals,j)=gel(xqPowers, 1+polyVals[j]*cycloOrder/charOrder);
                    }
                    else
                    {
                        gel(embedVals,j) = mkpolmod(gen_0, cycloPol);
                    }
                }
                GEN eisQ = eisSeriesQ(polyVals, coeffsneeded);
                eisQ = gsubst(eisQ, 0, gel(xqPowers, 1+cycloOrder/charOrder));
                eisQ = RgV_to_RgX(eisQ, 1);
                eisQ = RgXn_inv(eisQ, coeffsneeded);

                for(long i = 1; i<lg(formsInWt2); i++)
                {
                    GEN wt1Form = RgXn_mul(gconcat(gen_0,gel(formsInWt2,i)), eisQ, coeffsneeded);
                    wt1Form = RgX_to_RgC(wt1Form, coeffsneeded);
                    GEN fourierExpansion = lift(wt1Form);
                    long isPoly = 0;
                    for(long j = 2; j<lg(fourierExpansion); j++)
                    {
                        if(gequal0(gel(fourierExpansion, j))) continue;
                        gel(fourierExpansion,j) = QXQ_div(gel(fourierExpansion,j), gel(fourierExpansion,1), cycloPol);
                        if(degree(gel(fourierExpansion,j)))
                        {
                            isPoly = 1;
                        }
                    }
                    gel(fourierExpansion,1) = gen_1;
                    pari_printf("The form is %Ps\n", fourierExpansion);
                    if(isPoly) pari_printf("where x is some root of %Ps\n", gel(gel(wt1Form,1),1));
                    if(lg(gel(transformationData,3))-1==dihedralDim)
                    {
                        pari_printf("Projective image is Dn\n");
                        continue;
                    }
                    long zeroCount = 0;
                    //pari_printf("embedvals are %Ps\n", embedVals);
                    long nondihknown = 0;
                    long formKnown = 0;
                    for(long j=2; j<coeffsneeded; j=unextprime(j+1))
                    {
                        if(!umodiu(N,j)) continue;
                        if(gequal0(gel(fourierExpansion,j)))
                        {
                            zeroCount++;
                        }
                        else
                        {
                            zeroCount--;
                            GEN cg = gpowgs(gel(fourierExpansion,j), 2);
                            cg = gmul(cg, gel(embedVals, Fl_inv(umodsu(j,lg(embedVals)-1), lg(embedVals)-1)));
                            cg = lift(cg);
                            if(gequal(cg, gen_2))
                            {
                                if(nondihknown==2)
                                {
                                    pari_printf("Projective image is Dn\n");
                                    formKnown = 1;
                                    break;
                                }
                                nondihknown = 1;
                            }
                            if(degree(cg))
                            {
                                cg = gshift(cg,1);
                                cg = gsub(cg, stoi(3));
                                cg = RgXQ_pow(cg, gen_2, cycloPol);
                                if(gequal(cg,stoi(5)))
                                {
                                    if(nondihknown==1)
                                    {
                                        pari_printf("Projective image is Dn\n");
                                        formKnown = 1;
                                        break;
                                    }
                                    nondihknown = 2;
                                }
                                else
                                {
                                    pari_printf("Projective image is Dn\n");
                                    formKnown = 1;
                                    break;
                                }
                            }
                        }
                    }
                    if(formKnown) continue;
                    if(zeroCount>-5)
                    {
                        pari_printf("Projective image is probably Dn\n");
                    }
                    else
                    {
                        if(!nondihknown)
                        {
                            pari_printf("Projective image is probably A4\n");
                        }
                        else if(nondihknown==1)
                        {
                            if(dihedralDim)
                            {
                                pari_printf("Projective image is probably S4\n");
                            }
                            else
                            {
                                pari_printf("Projective image is S4\n");
                            }
                        }
                        else
                        {
                            if(dihedralDim)
                            {
                                pari_printf("Projective image is probably A5\n");
                            }
                            else
                            {
                                pari_printf("Projective image is A5\n");
                            }
                        }
                    }
                }
                set_avma(ltop);
                return;
            }
        }
    }
    if(!dihedralDim)
    {
        pari_printf("S_1^new(%Ps,chi_%Ps)=0\n", N, chiexp);
    }
    else if (dihedralDim==1)
    {
        pari_printf("There is 1 dihedral form in S_1^new(%Ps,chi_%Ps), but it wasn't explicitly computed.\n", N, chiexp);
    }
    else
    {
        pari_printf("There are %ld dihedral forms in S_1^new(%Ps,chi_%Ps), but they weren't explicitly computed\n", dihedralDim, N, chiexp);
    }
    set_avma(ltop);
}

long wt1newformDimFromExp(GEN N, GEN chiexp, GEN database)
{
    pari_sp ltop = avma;
    GEN group = znstar0(N, 1);
    GEN chiLog = znconreylog(group, chiexp);
    pari_printf("chiLog starts as %Ps\n", chiLog);
    chiLog = znconreychar(group, chiLog);
    chiLog = bestRep(group, chiLog);
    pari_printf("bestRep is %Ps\n", chiLog);
    long dim = wt1newformdimension(itos(N), chiLog, database);
    set_avma(ltop);
    return dim;
}

long doesFormEqualSpecificEis(GEN form, GEN eisForm, long fieldp)
{
    for(long p = 2; p<lg(form); p=unextprime(p+1))
    {
        if(form[p]!=eisForm[p]) return 0;
    }
    return 1;
}

long isFormFromEis(GEN form, GEN eisForms, long fieldp)
{
    for(long i = 1; i<lg(eisForms); i++)
    {
        if (doesFormEqualSpecificEis(form, gel(eisForms,i), fieldp)) return 1;
    }
    return 0;
}

GEN eisFormsFromVals(GEN eisForms, long numcoefs, long fieldp)
{
    for(long i = 1; i<lg(eisForms); i++)
    {
        GEN chi1vals = gel(gel(eisForms,i),1);
        GEN chi2vals = gel(gel(eisForms,i),2);
        GEN formCoefs = const_vecsmall(numcoefs,0);
        for(long p = 2; p<=numcoefs; p=unextprime(p+1))
        {
            long pmodchi1 = umodsu(p-1,lg(chi1vals)-1)+1;
            long pmodchi2 = umodsu(p-1,lg(chi2vals)-1)+1;
            if(chi1vals[pmodchi1]) formCoefs[p]=Fl_inv(gel(gel(eisForms,i),1)[pmodchi1],fieldp);
            if(gel(gel(eisForms,i),2)[pmodchi2]) formCoefs[p]=Fl_add(formCoefs[p],Fl_inv(gel(gel(eisForms,i),2)[pmodchi2],fieldp),fieldp);
        }
        gel(eisForms,i)=formCoefs;
    }
    return eisForms;
}

GEN removeEisFromDiagonalised(GEN diagonalised, GEN eisForms, long fieldp)
{
    GEN cleanedDiagonalised = cgetg(1,t_MAT);
    for(long i = 1; i<lg(diagonalised); i++)
    {
        if(isFormFromEis(gel(diagonalised,i),eisForms, fieldp)) continue;
        cleanedDiagonalised = vec_append(cleanedDiagonalised, gel(diagonalised,i));
    }
    return cleanedDiagonalised;
}

//The long returned here is the lifted level which can give rise to exotic reps
//If this is 0, there are no lifts to spaces containing exotic reps
long canHaveExotic(long N, GEN stats)
{
    if(uisprime(N))
    {
        if(umodsu(N,8)==1) return 0;
        if(umodsu(N,8)==5) return itos(zncharorder(znstar0(stoi(N),1), stats))==4;
        return itos(zncharorder(znstar0(stoi(N),1), stats))==2;
    }
    GEN group = znstar0(stoi(N),1);
    GEN fchi = zncharconductor(group, stats);
    GEN factors=myfactoru(N);
    long lift = 1;
    long liftsOrder5 = 1;
    long liftsOrder4 = 1;
    for(long i = 1; i<lg(gel(factors,1)); i++)
    {
        if(gel(factors,2)[i]==1 || gel(factors,2)[i]==Z_lval(fchi, gel(factors,1)[i]))
        {
            GEN chiQ = znchardecompose(group, stats, stoi(gel(factors,1)[i]));
            long order = itos(zncharorder(group, chiQ));
            if(order==1) return 0;
            if(order>5) lift*=gel(factors,1)[i];
            else if(order==5)
            {
                liftsOrder5*=gel(factors,1)[i];
            }
            else if (order==4)
            {
                liftsOrder4*=gel(factors,1)[i];
            }
        }
    }
    if(liftsOrder4>liftsOrder5) return lift*liftsOrder5;
    return lift*liftsOrder4;
}

long getNeededCoeffs(GEN database)
{
    if (gequal0(database) || lg(database)==1) return 0;
    return itos(gel(database,lg(database)-1));
}

long getDeflation(GEN P)
{
    long d = 0;
    for(long i = 1; i<lg(P); i++)
    {
        if(degree(gel(P,i))<1) continue;
        d = ugcd(d, ZX_deflate_order(gel(P,i)));
        if(d==1) return 1;
    }
    return d;
}


//Find the dimension of the weight 1 space of level N, with conrey logarithm stats, given the
//database of weight 2 forms, and known wt 1 dimensions of lower levels. The finite field will be
//congruent to 1 mod lcmwith.
GEN getWt1NewForms(long charOrder, long N, GEN stats, GEN polyVals, GEN database, long details)
{
    if(details) pari_printf("checking char %Ps\n", stats);
    //get the dimension of the oldspace, eisenstein space and dihedral space
    long oldDim = wt1oldformdimension(N,stats, database);
    GEN dividedSpace, eisForms, gcds = mkgcd(N);
    GEN eisStats = eisCharsAlt(N, gcds, stats);
    long eisDim = lg(eisStats)-1;
    //hasEis just indicates whether there are other Eisenstein series. If there are, we will
    //need an additional coefficient when dividing as they have constant 0.
    long hasEis = eisDim>0;
    long dihedralDim = getDihedralDim(N, stats, gel(database,3));

    //Dimension of the wt2 space
    long wt2dim = getSpaceDim(getWt2cuspspace(gel(database,2), N, 1));

    //No forms to compute
    if (wt2dim<=oldDim) return database;

    //How many coefficients can we currently construct a wt2 basis to
    long knownCoefsThisLevel = numcoefsknown(gel(database,2),N);

    //What prime p do we use to stabilise in the Hecke Stability Method
    long heckep = 2;
    while(!umodsu(N,heckep)) heckep = unextprime(heckep+1);

    //We can often initially stabilise by a lower prime, thus requiring fewer
    //coefficients as the dimension is reduced prior to stabilising by heckep
    //lowerMult is simply the first prime where the Eigenvalues are not definitely 0
    long lowerMult = 2;
    while(!uissquarefree(ugcd(N,lowerMult*lowerMult))) lowerMult++;

    //We may have already stored the number of coefficients to make the wt2 matrix full rank
    long coeffsneeded = getNeededCoeffs(gel(gel(database, 2), N));

    //In order to stabilise by lowerMult, we need up to lowerMult*coeffsneeded coefficient
    coeffsneeded *= lowerMult;

    if(details) pari_printf("expanding basis\n");

    //Do we have enough coefficients of the traceform? If not, compute more
    if(knownCoefsThisLevel<coeffsneeded+hasEis) expandBasisFor(gel(database,2), N, coeffsneeded+hasEis);

    //Matrix of coefficients in weight 2, not embedded into field
    GEN spaceInWt2 = getWt2cuspspace(gel(database,2), N, coeffsneeded);

    if(details) pari_printf("establishing field\n");
    //The field prime p must be congruent to 2 mod 2LCM(phi(N),D,60)
    long h = ulcm(eulerphiu(N), 60);
    h = ulcm(h, getDihedralLCM(N, stats, gel(database, 3)));
    h = ulcm(h, getOldLCM(N, stats, gel(database, 1)));
    h <<= 1;
    long fieldp = h+1;

    //Ensure that p is prime
ESTABLISHFIELD:
    while (!uisprime(fieldp) || !umodsu(N,fieldp)) fieldp += h;
    //Primitive element in Fp
    long primforp = itos(lift(znprimroot(stoi(fieldp))));

    if(details) pari_printf("prim for %ld is %ld\n", fieldp, primforp);
    //Fix element in Fp which is the order of the character chi
    long charOrderElt = Fl_powu(primforp, (fieldp-1)/charOrder, fieldp);
    //Using this, create a vector of evaluations of chi in Fp
    GEN embedVals = const_vecsmall(lg(polyVals)-1,0);
    for(long i = 1; i<lg(embedVals); i++)
    {
        if (polyVals[i]!=-1)
        {
            embedVals[i]=Fl_powu(charOrderElt, polyVals[i], fieldp);
        }
    }

    if(details) pari_printf("getting eisC to not be 0\n");
    //Compute the constant of the Eisenstein series attached to infinity
    long eisC = eisConst(embedVals, fieldp);
    //If this is zero, pick a different field
    if (!eisC)
    {
        fieldp += h;
        goto ESTABLISHFIELD;
    }

    if(details) pari_printf("embedding space\n");
    //Embed the weight 2 space into the field
    GEN embedWt2Bas = embedWt2Space(spaceInWt2, fieldp, primforp);

    if(details)
    {
        pari_printf("checking rank\n");
        pari_printf("num coefs is %ld, is this enough?\n", coeffsneeded);
        pari_printf("rank is %ld\n", Flm_rank(embedWt2Bas, fieldp));
    }

    //If the weight 2 space isn't full rank in the field, switch it
    if(Flm_rank(embedWt2Bas, fieldp)<lg(embedWt2Bas)-1)
    {
        fieldp+=h;
        goto ESTABLISHFIELD;
    }

    if(details) pari_printf("dividing by eis\n");
    //Compute the rest of the Eisenstein series attached to infinity
    GEN eisInf = eisSeries(embedVals, coeffsneeded, fieldp, eisC);

    //Divided the weight 2 matrix by this Eisenstein series
    dividedSpace = divideBasisByEis(embedWt2Bas, eisInf, fieldp);

    if(details) pari_printf("dividing by further eis\n");
    //If there are other Eisenstein series, divide by these also
    if (eisDim)
    {
        //Compute the subspace of the weight 2 cuspform space with first 2 coefficients 0
        GEN superCuspidalSpace = extendWt2cuspspace(gel(database,2), N, spaceInWt2, coeffsneeded+1);
        GEN altMult, eis;
        embedWt2Bas = embedWt2Space(superCuspidalSpace, fieldp, primforp);
        embedWt2Bas = getCuspidalUpTo(embedWt2Bas, 1, fieldp);


        if(lg(embedWt2Bas)-1==oldDim) return database;
        //Find all of the chi values of relevant Eisenstein series
        eisForms = eisValsFromChiStats(N, stats, fieldp, eisStats, primforp);
        pari_sp topOfEisDiv = avma;
        GEN intersection = shallowcopy(dividedSpace);
        intersection = rowslice(intersection, 1, coeffsneeded/lowerMult);
        for(long i = 1; i<lg(eisForms); i++)
        {
            //Compute the Eisenstein series
            eis = eisFromChiVals(fieldp, coeffsneeded/lowerMult, gel(eisForms, i), 1);
            //If this is the first additional division, just divide as normal and
            //then take the intersection with the division by the Eisenstein at infinity
            if(i==1)
            {
                if(details) pari_printf("doing first additional division\n");
                altMult = divideBasisByEis(rowslice(embedWt2Bas, 2, coeffsneeded/lowerMult+1), eis, fieldp);
                intersection = Flm_intersect(intersection, altMult, fieldp);
                intersection = gerepileupto(topOfEisDiv, intersection);
                if(lg(intersection)-1==oldDim) return database;
                if(lg(intersection)-1==oldDim+dihedralDim) break;
            }
            //Otherwise, we reduce the computation by multiplying the existing weight 1 space
            //and taking the intersection at weight 2 before dividing again
            else
            {
                if(details) pari_printf("doing further additional divisions\n");
                altMult = multiplyMatByEis(intersection, Flv_to_Flx(eis,0), fieldp);
                altMult = Flm_intersect(rowslice(embedWt2Bas,2,1+coeffsneeded/lowerMult), altMult, fieldp);
                if(lg(altMult)-1==oldDim) return database;
                intersection = divideBasisByEis(altMult, eis, fieldp);
                intersection = gerepileupto(topOfEisDiv, intersection);
                if(lg(intersection)-1==oldDim+dihedralDim) break;
            }
        }
        //Everything has been done at the smallest possible submatrix, so now we recover the
        //full matrix via transformation from the initial divided space
        GEN transformation = Flm_gauss(rowslice(dividedSpace,1,coeffsneeded/lowerMult), intersection, fieldp);
        dividedSpace = Flm_mul(dividedSpace, transformation, fieldp);
        dividedSpace = gerepileupto(topOfEisDiv, dividedSpace);
    }
    if(lg(dividedSpace)-1==oldDim) return database;

    if(details) pari_printf("stabilising\n");

    if(details) pari_printf("length of divided space is %ld while olddim is %ld and dihedral dim is %ld\n", lg(dividedSpace), oldDim, dihedralDim);

    GEN stable;
    //If everything that remains is explained by oldforms or dihedrals then no stabilisation
    //is needed.
    if(lg(dividedSpace)-1==oldDim+dihedralDim)
    {
        stable = dividedSpace;
    }
    else
    {
        //Stabilise up to heckep
        stable = stabiliseUpTo(gcds, embedVals, dividedSpace, heckep, fieldp, oldDim+dihedralDim);
        if(lg(stable)-1==oldDim) return database;
    }

    if(details) pari_printf("length of stable is %ld\n", lg(stable));
    //If everything is explained by oldforms or dihedrals, then we may not need to
    //compute specifics
    if(lg(stable)-1==oldDim+dihedralDim)
    {
        if (N>(lg(gel(database,2))-1)>>1)
        {
            return database;
        }
        else if (odd(N))
        {
            if (N>(lg(gel(database,2))-1)/3)
            {
                return database;
            }
            else if (umodsu(N,3))
            {
                if (N>(lg(gel(database,2))-1)>>2)
                {
                    return database;
                }
            }
        }
    }

    if(details) pari_printf("getting oldforms\n");
    //Recover the oldforms, embedding them into the field
    GEN oldForms = getKnownForms(embedVals, gel(database,2), N, stats, gel(database,1), fieldp, primforp, coeffsneeded, eisInf, stable);
    //Construct the matrix with new forms on the right
    for(long i = 1; i<lg(stable); i++)
    {
        if(lg(oldForms)==lg(stable)) break;
        if(Flm_Flc_invimage(oldForms, gel(stable,i), fieldp)==NULL)
        {
            oldForms = vec_append(oldForms, gel(stable,i));
        }
    }

    stable = oldForms;

    if(details) pari_printf("diagonalising\n");

    if(details) pari_printf("stable is length %ld and rank %ld\n", lg(stable), Flm_rank(stable, fieldp));

    //Diagonalise the space
    GEN diagonalised;
    diagonalised = diagonalise(gcds, embedVals, oldDim, stable, fieldp);

    if (typ(diagonalised)==t_INT)
    {
        embedWt2Bas = embedWt2Space(spaceInWt2, fieldp, primforp);
        GEN altMult = multiplyMatByEis(stable, Flv_to_Flx(eisInf,0), fieldp);
        GEN transformation = Flm_gauss(rowslice(embedWt2Bas,1,nbrows(altMult)), altMult, fieldp);
        pari_sp diagtop = avma;
        while(typ(diagonalised)==t_INT){
        if(details) pari_printf("needed more coeffs to diagonalise!\n");
        if(details) pari_printf("currently have %ld coefficients\n", coeffsneeded);
        if(details) pari_printf("tried to diagonalise by %ld but couldn't\n", -itos(diagonalised));
        //Needed more coefficients to diagonalise
        coeffsneeded/=lowerMult;
        while(Flm_inv(rowslice(stable, 1, coeffsneeded), fieldp)!=NULL){
            coeffsneeded-=2;
        }
        coeffsneeded+=2;
        coeffsneeded*=-itos(diagonalised);
        if(details) pari_printf("going to compute %ld\n", coeffsneeded);
        if(knownCoefsThisLevel<coeffsneeded) expandBasisFor(gel(database,2), N, coeffsneeded);
        database = gerepilecopy(diagtop, database);
        GEN tempWt2 = extendWt2cuspspace(gel(database,2), N, spaceInWt2, coeffsneeded);
        GEN tempWt2Bas = embedWt2Space(tempWt2, fieldp, primforp);
        GEN tempEis = extendEisSeries(eisInf, embedVals, coeffsneeded, fieldp);
        GEN altMult = Flm_mul(tempWt2Bas, transformation, fieldp);
        GEN tempStable = divideBasisByEis(altMult, tempEis, fieldp);
        diagonalised = diagonalise(gcds, embedVals, oldDim, tempStable, fieldp);
        }
    }

    if(lg(diagonalised)==1) return database;

    GEN satakes = basisToSatake(gcds, N, diagonalised, embedVals, fieldp, primforp);

    if(lg(satakes)==1) return database;

    if(lg(satakes)==dihedralDim+1){
        if (gequal0(gel(gel(database,1),N)))
        {
            gel(gel(database,1),N) = mkvec(mkvec2(stats, satakes));
        }
        else
        {
            gel(gel(database,1),N) = vec_append(gel(gel(database,1),N), mkvec2(stats, satakes));
        }
        return database;
    }

    //To verify, we need far fewer coordinates, only up to the full-rank point
    coeffsneeded = getNeededCoeffs(gel(gel(database, 2), N));

    if(details) pari_printf("num elts is %ld while dihedral dim is %ld and old dim is %ld\n", lg(diagonalised)-1, dihedralDim, oldDim);

    if(details) pari_printf("getting satake\n");

    GEN transformations = cgetg(1,t_MAT);

    if(dihedralDim){
        GEN dihedralImages = getDihedralImages(N, stats, gel(database,3));
        dihedralImages = vec_to_vecsmall(dihedralImages);
        for(long i = 1; i<lg(dihedralImages); i++){
            dihedralImages[i] = ulcm(dihedralImages[i], charOrder);
        }
        GEN nonDihSatakes = cgetg(1,t_MAT);
        GEN dihSatakes = cgetg(1,t_MAT);
        for(long i = 1; i<lg(satakes); i++){
            long couldBeDihedral = 0;
            long satakeDiv = ulcm(gel(satakes,i)[1], charOrder);
            for(long j = 1; j<lg(dihedralImages); j++){
                if(umodsu(satakeDiv,dihedralImages[j])==0){
                    couldBeDihedral = 1;
                    break;
                }
            }
            if (!couldBeDihedral){
                nonDihSatakes = vec_append(nonDihSatakes, gel(satakes,i));
            } else {
                dihSatakes = vec_append(dihSatakes, gel(satakes,i));
            }
        }
        if(lg(dihSatakes)-1==dihedralDim){
            transformations = gcopy(dihSatakes);
            satakes = gcopy(nonDihSatakes);
        }
    }

    if(details) pari_printf("Got Satake, establishing Q stuff\n");

    long cycloOrder = charOrder;

    for(long i = 1; i<lg(satakes); i++)
    {
        cycloOrder = ulcm(cycloOrder, gel(satakes,i)[1]);
    }

    GEN cycloPol = polcyclo(cycloOrder, 0);
    GEN xqPowers = RgXQ_powers(pol_x(0), cycloOrder-1, cycloPol);
    for(long i = 1; i<lg(xqPowers); i++)
    {
        gel(xqPowers, i) = mkpolmod(gel(xqPowers, i), cycloPol);
    }

    if(details) pari_printf("inverting wt 2 space\n");

    spaceInWt2 = rowslice(spaceInWt2, 1, coeffsneeded);

    GEN inversionDetails = gel(database,4);
    GEN wt2inv = gel(inversionDetails,1);
    GEN pv = gel(inversionDetails, 2);
    GEN den = gel(inversionDetails, 3);

    if(details) pari_printf("computing Eis series over Q \n");

    GEN eisQ = gconcat(gen_0,eisSeriesQ(polyVals, coeffsneeded));

    pari_sp aboveSatakeCheck = avma;
    for(long i = 1; i<lg(satakes); i++)
    {
        if(details) pari_printf("checking %ld-th satake\n", i);
        long definedOver = ulcm(charOrder, gel(satakes,i)[1]);
        GEN defpol = polcyclo(definedOver, 0);
        GEN purportedQform = gconcat(gen_0,liftSatakeToQ(N, gel(satakes,i), polyVals, coeffsneeded, definedOver, charOrder));
        purportedQform = gsubst(purportedQform, 0, mkpolmod(pol_x(0),defpol));
        GEN eisQLift = gsubst(eisQ, 0, mkpolmod(ZX_rem(pol_xn(definedOver/charOrder, 0), defpol), defpol));
        GEN wt2check = RgXn_mul(eisQLift, purportedQform, coeffsneeded);

        wt2check = RgX_to_RgC(wt2check, coeffsneeded);
        //GEN altTransform = gauss(spaceInWt2, mkmat(lift(wt2check)));
        GEN altTransform = ZXQM_mul(wt2inv, extract0(mkmat(lift(wt2check)),gel(pv,1), mkvecsmall(1)), defpol);
        GEN firstCheck = ZXQM_mul(spaceInWt2, altTransform, defpol);
        GEN secondCheck = gmul(wt2check, den);
            long isequal = gequal(gel(firstCheck,1), secondCheck);
            if(details) pari_printf("adding to transformations? %ld\n", isequal);
            if(isequal)
            {
                transformations = vec_append(transformations, gel(satakes,i));
            }
        transformations = gerepilecopy(aboveSatakeCheck, transformations);

    }
    if(lg(transformations)>1)
    {
        if (gequal0(gel(gel(database,1),N)))
        {
            gel(gel(database,1),N) = mkvec(mkvec2(stats, transformations));
        }
        else
        {
            gel(gel(database,1),N) = vec_append(gel(gel(database,1),N), mkvec2(stats, transformations));
        }
    }

    return database;
}

GEN getTraceVec(GEN group, GEN chiL)
{
    long order = itos(zncharorder(group, chiL));
    GEN cycloPol = polcyclo(order, 0);
    GEN nf = nfinit(cycloPol, 5);
    GEN normal = znconreylog_normalize(group, chiL);
    GEN vals = ncharvecexpo(group, normal);
    GEN lexico = const_vecsmall(lg(vals), order);
    for(long i=1; i<lg(vals); i++)
    {
        if(vals[i]==-1)
        {
            lexico[i+1]=0;
        }
        else
        {
            lexico[i+1] = itos(nftrace(nf, pol_xn(vals[i],0)));
        }
    }
    return lexico;
}

//GEN myLowStackInverse

GEN updateDatabaseForLevel(GEN database, long N, long maxM)
{
    //Set details = 1 for very verbose output
    //Set details = 0 for normal running
    long details = 0;
    if(details) pari_printf("finding all characters\n");
    GEN stats = getAltCharStats(N);

    if(details) pari_printf("checking if we need to compute anything\n");

    long willcompsomething = 0;
    for (long i = 1; i<lg(stats); i++)
    {
        long exoticLift = canHaveExotic(N, gel(stats,i));
        //If we cannot lift to a level with exotics, don't need to compute
        if (!exoticLift) continue;
        //If the nearest lift to a space with possible exotics is beyond what we're aiming for,
        //and we know the dihedrals are at this level, no need to compute
        if(N<lg(gel(database,3)) && N>maxM/exoticLift)
        {
            continue;
        }
        //If the space itself cannot have exotics and there are no dihedral forms, no need to compute
        if(exoticLift>1 && !getDihedralDim(N, gel(stats,i), gel(database,3)))
        {
            continue;
        }
        willcompsomething = 1;
        break;
    }

    if(!willcompsomething && (N>maxM/2 || (odd(N)&&N>maxM/3)))
    {
        return database;
    }

    if(details) pari_printf("checking the weight 2 info\n");

    GEN group = znstar0(stoi(N),1);


    pari_sp veryTop = avma;

    char filename[20];
    char dummyfilename[20];
    sprintf(filename, "wt2spaces/%ld.txt", N);
    sprintf(dummyfilename, "dummies2/%ld.txt", N);
    FILE *dummy_file = fopen(dummyfilename, "w");
    flock(fileno(dummy_file), LOCK_EX);
    FILE *in_file = fopen(filename, "r");
    if(in_file != NULL)
    {
        gel(gel(database,2),N) = gp_read_file(filename);
        fclose(in_file);
        flock(fileno(dummy_file), LOCK_UN);
    }
    else
    {
        flock(fileno(dummy_file), LOCK_UN);
        if(details) pari_printf("initialising weight 2 space\n");
        gel(gel(database,2),N) = initialiseWt2Space(N, details);
    }
    fclose(dummy_file);

    if(willcompsomething) {

            if(details) pari_printf("getting all other levels into database\n");

    GEN divs = divisorsu(N);
    for(long i = 2; i<lg(divs)-1; i++)
    {
        if (divs[i]<11) continue;
        if(vecsearch(mkvecsmalln(7, 12, 13, 16, 18, 25, 28, 60), stoi(divs[i]), NULL)>0) continue;
        sprintf(filename, "wt2spaces/%ld.txt", divs[i]);
        sprintf(dummyfilename, "dummies2/%ld.txt", divs[i]);
        dummy_file = fopen(dummyfilename, "w");
        flock(fileno(dummy_file), LOCK_EX);
        in_file = fopen(filename, "r");
        gel(gel(database,2),divs[i]) = gp_read_file(filename);
        fclose(in_file);
        flock(fileno(dummy_file), LOCK_UN);
        fclose(dummy_file);
        sprintf(filename, "wt1spaces/%ld.txt", divs[i]);
        sprintf(dummyfilename, "dummies1/%ld.txt", divs[i]);
        dummy_file = fopen(dummyfilename, "w");
        flock(fileno(dummy_file), LOCK_EX);
        in_file = fopen(filename, "r");
        gel(gel(database,1),divs[i]) = gp_read_file(filename);
        fclose(in_file);
        flock(fileno(dummy_file), LOCK_UN);
        fclose(dummy_file);
    }

    //Expand and invert
    long knownCoefsThisLevel = numcoefsknown(gel(database,2),N);
    //lowerMult is simply the first prime where the Eigenvalues are not definitely 0
    long lowerMult = 2;
    while(!uissquarefree(ugcd(N,lowerMult*lowerMult))) lowerMult++;
    //We may have already stored the number of coefficients to make the wt2 matrix full rank
    long coeffsneeded = getNeededCoeffs(gel(gel(database, 2), N));
    //If not, "guess" 2 more than the dimension
    long wt2dim = getSpaceDim(getWt2cuspspace(gel(database,2), N, 1));
    if(!wt2dim) return database;
    if (!coeffsneeded) coeffsneeded = wt2dim+2;
    //In order to stabilise by lowerMult, we need up to lowerMult*coeffsneeded coefficient
    coeffsneeded *= lowerMult;

    if(details) pari_printf("expanding from %ld coefficients to %ld\n", coeffsneeded/lowerMult, coeffsneeded);
    //Do we have enough coefficients of the traceform? If not, compute more
    if(knownCoefsThisLevel<coeffsneeded+1) expandBasisFor(gel(database,2), N, coeffsneeded+1);
    if(details) pari_printf("done expansion, getting cuspspace\n");
    //Matrix of coefficients in weight 2, not embedded into field
    GEN spaceInWt2 = getWt2cuspspace(gel(database,2), N, coeffsneeded);

    if(!getNeededCoeffs(gel(gel(database, 2), N)))
    {
        if(details) pari_printf("expanding to max rank needed\n");
        if(details) pari_printf("weight 2 space is length %ld\n", lg(spaceInWt2)-1);
        if(details) pari_printf("first two rows are %Ps\n", rowslice(spaceInWt2,1,2));
        GEN pv = ZM_indexrank(spaceInWt2);
        pv = gel(pv,1);
        long firstFullRankRow = pv[lg(pv)-1];
        coeffsneeded = (firstFullRankRow+2)*lowerMult;
        if(knownCoefsThisLevel<coeffsneeded+1) expandBasisFor(gel(database,2), N, coeffsneeded+1);
        //Note down the number of coefficients needed, and save this to disc
        gel(gel(gel(database, 2), N), lg(gel(gel(database, 2), N))-1) = stoi(coeffsneeded/lowerMult);
        char filename[20];
        sprintf(filename, "wt2spaces/%ld.txt", N);
        char dummyfilename[20];
        sprintf(dummyfilename, "dummies2/%ld.txt", N);
        FILE *dummy_file = fopen(dummyfilename, "w");
        flock(fileno(dummy_file), LOCK_EX);
        FILE *out_file = fopen(filename, "w");
        pari_fprintf(out_file, "%Ps\n", gel(gel(database,2),N));
        fclose(out_file);
        flock(fileno(dummy_file), LOCK_UN);
        fclose(dummy_file);
    }

    if(lg(database)==4){
    database = vec_append(database, gen_0);
    }

    if(details) pari_printf("inverting wt 2 basis\n");
    GEN pv, den;
    GEN wt2inv = ZM_pseudoinv(spaceInWt2, &pv, &den);
    gel(database,4) = mkvec3(wt2inv,pv, den);
    database = gerepilecopy(veryTop, database);

    if(details) pari_printf("inverted. Resetting stack size\n");

    paristack_resize(250000000);

    if(details) pari_printf("Stack size reset\n");

    for (long i = 1; i<lg(stats); i++)
    {
        long exoticLift = canHaveExotic(N, gel(stats,i));
        //If we cannot lift to a level with exotics, don't need to compute
        if (!exoticLift) continue;
        //If the nearest lift to a space with possible exotics is beyond what we're aiming for,
        //and we know the dihedrals are at this level, no need to compute
        if(N<lg(gel(database,3)) && N>maxM/exoticLift)
        {
            continue;
        }
        //If there are no exotics, and no dihedrals, no need to compute
        if(exoticLift>1 && !getDihedralDim(N, gel(stats,i), gel(database,3)))
        {
            continue;
        }
        GEN chiPrim = znchartoprimitive(group, gel(stats,i));
        GEN normal = znconreylog_normalize(gel(chiPrim,1), gel(chiPrim,2));
        long charOrder = itos(zncharorder(group, gel(stats,i)));
        GEN vals = ncharvecexpo(gel(chiPrim,1), normal);
        database = getWt1NewForms(charOrder, N, gel(stats,i), vals, database, details);
        database = gerepilecopy(veryTop, database);
    }
    }
    sprintf(filename, "wt1spaces/%ld.txt", N);
    sprintf(dummyfilename, "dummies1/%ld.txt", N);
    dummy_file = fopen(dummyfilename, "w");
    flock(fileno(dummy_file), LOCK_EX);

    FILE *out_file = fopen(filename, "w");
    pari_fprintf(out_file, "%Ps\n", gel(gel(database,1),N));
    fclose(out_file);
    flock(fileno(dummy_file), LOCK_UN);
    fclose(dummy_file);

    return database;
}

long verifywt2(long N)
{
    pari_sp ltop = avma;
    char filename[20];
    sprintf(filename, "wt2spaces/%ld.txt", N);
    FILE *in_file = fopen(filename, "r");
    GEN wt2struct;
    if(in_file==NULL)
    {
        wt2struct = initialiseWt2Space(N, 0);
    }
    else
    {
        wt2struct = gp_read_file(filename);
        fclose(in_file);
    }

    long numKnown = coefsKnownSpecific(wt2struct);


    GEN spaceInWt2 = getWt2newspace(N, wt2struct, 1, numKnown);


    GEN mf = mfinit(mkvec2(stoi(N), gen_2), 0);
    GEN M2 = cgetg(itos(mfdim(mkvec2(stoi(N),gen_2),0))+1, t_MAT);
    GEN mBas = mfbasis(mf, 0);
    for(long i = 1; i<lg(M2); i++)
    {
        GEN basElt = gel(mBas,i);
        gel(M2,i) = mfcoefs(basElt, nbrows(spaceInWt2), 1);
    }
    M2 = rowslice(M2,2,lg(gel(spaceInWt2,1)));
    if (lg(M2)!=lg(spaceInWt2))
    {
        pari_printf("my space is %Ps\n", spaceInWt2);
        pari_printf("M2 is %Ps\n", M2);
        pari_printf("lengths differ?\n");
        set_avma(ltop);
        return 0;
    }
    GEN gauss = ZM_gauss(spaceInWt2, M2);
    if(gauss==NULL)
    {
        pari_printf("my space is %Ps\n", spaceInWt2);
        pari_printf("M2 is %Ps\n", M2);
        pari_printf("gauss was null?\n");
        set_avma(ltop);
        return 0;
    }
    long correct = ZM_equal(QM_mul(spaceInWt2, gauss), M2);
    if(!correct)
    {
        pari_printf("my space is %Ps\n", spaceInWt2);
        pari_printf("M2 is %Ps\n", M2);
        pari_printf("mul didn't equal\n");
    }
    set_avma(ltop);
    return correct;
}



void specifTrace(long N, long n)
{
    GEN factors = myfactoru(N);
    GEN stats = getRequiredStats(factors);
    //The square roots for M
    GEN sqrts = mksqr(N);
    //All of the groups for each prime (used to create the chi_p)
    GEN allgroups = getAllGroups(N);
    GEN stat = gel(stats,1);
    TwistChar psi = initialiseWt2TwistChar(N, stat, allgroups);
    psi.gcds = mkgcd(N);
    wt2trivialTraceByPsi(sqrts, n, psi, 1);
}



