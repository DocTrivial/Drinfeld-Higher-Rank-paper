#include <NTL/ZZ_pE.h>
#include <NTL/ZZ_pEX.h>
#include <NTL/vec_ZZ_p.h>
#include<NTL/mat_ZZ_pE.h>

#include <NTL/ZZ_pXFactoring.h>
#include <NTL/ZZ_pEXFactoring.h>
//#include <math.h>
#include <iostream>
#include <algorithm>
#include <cmath>
#include <fstream>
#include <vector>

using namespace std;
using namespace NTL;



// Generic function definitions
int ilog(double base, double targ) {
    return (int) (ilogb(targ)/ ilogb(base));
}

// makes map a random polynomial of degree = size-1
void random_map(ZZ_pX& map, int size) {
    map = random_ZZ_pX(size);
    while (coeff(map, size-1) == 0)
        SetCoeff(map, size-1, random_ZZ_p());
}

// res = dotproduct(map, elem)
// output can alias input
void apply_map(ZZ_pE& res, ZZ_pX& map, ZZ_pE& elem) {
    ZZ_pE tres = to_ZZ_pE(0);
    ZZ_pX op = rep(elem);
    int range = min(deg(map), deg(op));
    for (int i = 0; i < range; i++) 
        tres += map[i] * conv<ZZ_p>(op[i]); // need to fix this for general base fields
    res = tres;
}

// res = dotproduct(map, elem)
// output can alias input
void apply_map(ZZ_p& res, ZZ_pX& map, ZZ_pE& elem) {
    ZZ_p tres = to_ZZ_p(0);
    ZZ_pX op = rep(elem);
    int range = min(deg(map), deg(op));
    for (int i = 0; i < range; i++) {
        tres += map[i] * op[i]; // need to fix this for general base fields
    }
    res = tres;
}

// procedural version of the above
ZZ_p apply_map(ZZ_pX& map, ZZ_pE& elem) {
    ZZ_p tmp;
    apply_map(tmp, map, elem);
    return tmp;
}

// output can alias input
void operator_eval(ZZ_pE& res, Vec<ZZ_pE>& op, ZZ_pE& elem, long q ) {
    ZZ_pE tres = to_ZZ_pE(0);
    Vec<ZZ_pE> powers;
    powers.SetLength(op.length());
    powers[0] = elem;
    for (int i = 0; i < op.length(); i++) {
        if (i < op.length() - 1) {
            power(powers[i+1], powers[i], q);
        }
        tres += powers[i] * op[i];
    }
    res = tres;
}

void operator_eval(ZZ_pE& res, ZZ_pE& op, ZZ_pE& elem, long q ) {
    Vec<ZZ_pE> powers;
    ZZ_pX repp = rep(op);
    long d = deg(repp);
    if (d == -1) 
    {
        res = 0;
        return;
    }
    ZZ_pE tres = to_ZZ_pE(0);
    powers.SetLength(d + 1);
    powers[0] = 1;
    for (int i = 0; i <= d; i++) {
        if (i < d) 
            mul(powers[i+1], powers[i], elem);
        tres += powers[i] * repp[i];
    }
    res = tres;
}

void operator_eval(ZZ_pE& res, ZZ_pX& op, ZZ_pE& elem, long q ) {
    Vec<ZZ_pE> powers;
    long d = deg(op);
    if (d == -1) {
        res = 0;
        return;
    }
    ZZ_pE tres = to_ZZ_pE(0);
    powers.SetLength(d + 1);
    powers[0] = 1;
    for (int i = 0; i <= d; i++) {
        if (i < d) 
            mul(powers[i+1], powers[i], elem);
        res += powers[i] * op[i];
    }
    res = tres;
}


void build_poly(ZZ_pX& poly, int* arr, int len) {
    poly.SetLength(len);
    for (int i = 0; i < len; i++) {
        poly[i] = conv<ZZ_p>(ZZ(arr[i]));
    }
    return;
}

void elem_exp(mat_ZZ_pE& ret, mat_ZZ_pE& matr, double expo ) {
    for (int i = 0; i < 2; i++) {
        for (int j = 0; j < 2; j++) {
            power(ret[i][j], matr[i][j], expo);
        }
    }
    return;
}

void elem_exp(mat_ZZ_pE& ret, mat_ZZ_pE& matr, double q, double expo ) {
    ZZ_pX cons = ZZ_pX(INIT_MONO, 1, 1);
    ZZ_pE mono = conv<ZZ_pE>(cons);
    ZZ_pE xq;
    ZZ_pE temp;
    power(xq, mono, q);
    for (int i = 0; i < 2; i++) {
        for (int j = 0; j < 2; j++) {
            if (matr[i][j] == 0) {
                ret[i][j] = 0;
            }
            else {
                ret[i][j] = matr[i][j];
                for (int k = 0; k < expo; k++) {
                    operator_eval(temp, ret[i][j], xq, 1 );
                    ret[i][j] = temp;
                }
            }
        }
    }
    return;
}


void frob(ZZ_pE& ret, ZZ_pE& matr, double q, double expo ) {
    ZZ_pX cons = ZZ_pX(INIT_MONO, 1, 1);
    ZZ_pE mono = conv<ZZ_pE>(cons);
    ZZ_pE xq, temp;
    power(xq, mono, q);
    if (matr == 0) {
        ret = 0;
    }
    else {
        ret = matr;
        for (int k = 0; k < expo; k++) {
            operator_eval(temp, ret, xq, 1 );
            ret = temp;
        }
    }
    return;
}

void rtrace(ZZ_pE& res, ZZ_pE& elem, long q, int m, int n) {
    ZZ_pE ret = elem, incr = elem, temp;
    for (int i = 0; i < n - m; i += m ) {
        frob(temp, incr, q, m);
        //cout << "temp " << i << ": " << temp << endl;
        ret += temp;
        incr = temp;
    }
    res = ret;
}

ZZ_pE rtrace(ZZ_pE& elem, long q, int m, int n) {
    ZZ_pE rtra;
    rtrace(rtra, elem, q, m, n);
    return rtra;
}


//-------------------------------------------------
// computes values = [first, phit(first), ..] 
// output length = len
//-------------------------------------------------
void sequence_phis(Vec<ZZ_pE>& values, Vec<ZZ_pE>& phit, ZZ_pE& first, long len, long q)
{
    values.SetLength(len);
    values[0] = first;
    for (long i = 1; i < len; i++)
        operator_eval(values[i], phit, values[i-1], q);
}

//-------------------------------------------------
// returns ell(F)
//-------------------------------------------------
ZZ_p eval(const Vec<ZZ_p>& ell, const ZZ_pE& F)
{
    ZZ_p res = to_ZZ_p(0);
    for (long i = 0; i < ell.length(); i++)
        res += ell[i] * coeff(F._ZZ_pE__rep, i);
    return res;
}

//-------------------------------------------------
// resizes a vector of linear forms to length size
// all new entries are random of length n
//-------------------------------------------------
void set_to_size(Vec<Vec<ZZ_p>>& ell, long size, long n)
{
    long old = ell.length();
    ell.SetLength(size);
    for (long j = old; j < size; j++)
    {
        ell[j].SetLength(n);
        for (long i = 0; i < n; i++)
            ell[j][i] = random_ZZ_p();
    }
}

//-------------------------------------------------
// increases ell's size by 1
//-------------------------------------------------
void increment_size(Vec<Vec<ZZ_p>>& ell, long n)
{
    set_to_size(ell, ell.length()+1, n);
}

//-------------------------------------------------
// resizes a vector of ZZ_pE's to length size
// all new entries are random 
//-------------------------------------------------
void set_to_size(Vec<ZZ_pE>& alpha, long size)
{
    long old = alpha.length();
    alpha.SetLength(size);
    for (long j = old; j < size; j++)
        alpha[j] = random_ZZ_pE();
}

//-------------------------------------------------
// increases alpha's size by 1
//-------------------------------------------------
void increment_size(Vec<ZZ_pE>& alpha)
{
    set_to_size(alpha, alpha.length()+1);
}

//--------------------------------------------
// computes the charpoly of (g, del)
// P defines the kernel of gamma 
// inclusion = gamma(x) \in L
// Monte Carlo algorithm; uses several ell's and alpha's
//--------------------------------------------
ZZ_pX char_poly1(ZZ_pE& g, ZZ_pE& del, ZZ_pX& P, ZZ_pE& inclusion) {

    int q = conv<long>(ZZ_p::modulus());
    int n = deg(ZZ_pE::modulus());
    int d = deg(P);
    int m = n / d;
    int cnum = n/2 + 1;

    ZZ_pX B = pow(-1,n) * inv(norm(del)) * power(P,m);

    Vec<ZZ_pE> phit;
    phit.SetLength(3);
    phit[0] = inclusion;
    phit[1] = g;
    phit[2] = del;

    Vec<Vec<ZZ_p>> vec_ell;
    Vec<ZZ_pE> alpha;
    Vec<Vec<ZZ_pE>> vec_phis;

    long done = 0;
    long len = 2*n;
    ZZ_pX gen;
    ZZ_pX gammaX;
    Vec<ZZ_pX> seq_values;
    seq_values.SetLength(len);

    do
    {
        ZZ_pX old_gamma = gammaX;
        clear(gammaX);
        done = 1;

        increment_size(vec_ell, n);
        increment_size(alpha);

        long len_vec_ell = vec_ell.length();
        vec_phis.SetLength(len_vec_ell);
        sequence_phis(vec_phis[len_vec_ell-1], phit, alpha[len_vec_ell-1], len, q);
        
        gen = BuildIrred_ZZ_pX(len_vec_ell);

        for (long i = 0; i < len; i++)
        {        
            seq_values[i] = 0;
            for (long u = 0; u < len_vec_ell; u++)
                for (long v = 0; v < len_vec_ell; v++)
                SetCoeff(seq_values[i], u+v, eval(vec_ell[u], vec_phis[v][i]));
            seq_values[i] %= gen;
        }
        
        { 
            ZZ_pEPush push(gen); 
            Vec<ZZ_pE> seq_valuesE;
            seq_valuesE.SetLength(len);
            for (long i = 0; i < len; i++)
                seq_valuesE[i] = to_ZZ_pE(seq_values[i]);
            ZZ_pEX gamma = MinPolySeq(seq_valuesE, n);
            long nu = deg(gamma);
            for (long i = 0; i <= nu; i++)
            {
                if (deg(gamma[i]._ZZ_pE__rep) > 0)
                {
                    done = 0;
                    break;
                }
                SetCoeff(gammaX, i, coeff(gamma[i]._ZZ_pE__rep, 0));
            }
        }
        if (gammaX != old_gamma)
            done = 0;
    }
    while (done == 0);

    long nu = deg(gammaX);

// TODO: fix this!!!
    if (n && 1 == 0 && nu == n/2)
        Error("Not implemented yet");

    long len_vec_ell = vec_ell.length();
    Mat<ZZ_pX> A;
    A.SetDims(nu, nu);
    for (int i = 0; i < A.NumRows(); i++) 
        A[0][i] = seq_values[i];
    for (int i = 1; i < A.NumRows(); i++) 
    {
        for (int j = 0; j < A.NumRows() - 1; j++) 
            A[i][j] = A[i-1][j + 1];
        A[i][A.NumRows() - 1] = seq_values[A.NumRows() - 1 + i];
    }


    Vec<ZZ_pE> r;
    r.SetLength(len_vec_ell);
    for (long j = 0; j < len_vec_ell; j++)
    {
        ZZ_pE tmp = to_ZZ_pE(0);
        for (int i = 0; i <= deg(B); i++) 
            tmp += vec_phis[j][i] * B[i];
        r[j] = alpha[j] + tmp;
    }    

    
    Vec<ZZ_pX> b;
    b.SetLength(nu);
    
    for (long i = 0; i < nu; i++)
    {
        ZZ_pX tmp;
        clear(tmp);

        for (long u = 0; u < len_vec_ell; u++)
            for (long v = 0; v < len_vec_ell; v++)
                SetCoeff(tmp, u+v, eval(vec_ell[u], r[v]));
        b[i] = tmp % gen;

        for (long v = 0; v < len_vec_ell; v++)
            operator_eval(r[v], phit, r[v], q);
    }
    
    ZZ_pX poly;
    clear(poly);
    double begin = GetTime();
    { 
        ZZ_pEPush push(gen); 
        vec_ZZ_pE x;
        Mat<ZZ_pE> AE = conv<Mat<ZZ_pE>>(A);
        ZZ_pE det;
        Vec<ZZ_pE> BE = conv<Vec<ZZ_pE>>(b);
        solve(det, AE, x, BE);
        for (long i = 0; i < nu; i++)
            SetCoeff(poly, i, coeff(x[i]._ZZ_pE__rep, 0));
    }
    double end = GetTime();

#ifdef PROFILE
    cout << "Hankel System solving time: " << end-begin << endl;
#endif
    return poly;
}



ZZ_pX char_poly2(ZZ_pE& g, ZZ_pE& del, long p, long q_exp, int n, int m, ZZ_pX& P, ZZ_pE& inclusion) {

    int cnum = n/2 + 1, rnum = n, q = pow(p, q_exp), d = n/m;
    int tot = rnum + cnum, ind = 0;
    ZZ_pX b, cons = ZZ_pX(INIT_MONO, 1, 1);
    ZZ_pE mono = conv<ZZ_pE>(cons);
    ZZ_pE alpha, beta, bei;
    ZZ_pE monop = inclusion;

    b = pow(-1,n) * inv(norm(del)) * power(P,m);

    vec_ZZ_pE ei;
    vec_ZZ_pE rvals;
    ZZ_pEX interpol;

    ZZ_pX elem;
    ei.SetLength(cnum);
    rvals.SetLength(cnum);

    int maxdeg = ilog(p, cnum);
    elem.SetLength(maxdeg);

    for (int i = 0; i < cnum; i++) {
        ei[i] = conv<ZZ_pE>(ZZ(i));
        alpha = (-1)*(monop - ei[i]) / del;
        beta = (-1)*g / del;
        ind = 0;

        mat_ZZ_pE M, B, N, temp;
        N.SetDims(2,2);
        B.SetDims(2,2);
        M.SetDims(2,2);
        M[0][0] = 0;
        M[1][0] = 1;
        M[0][1] = alpha;
        M[1][1] = beta;
        B = M;
        N = M;

        while(2*ind + 1 < n) {
            elem_exp(B, M, q, ind + 1);
            mul(temp,M,B);
            M = temp;
            (ind*=2)++;
            //cout << M << endl;
        }

        elem_exp(B, N, q, ind);

        while (ind + 1 < n) {
            elem_exp(B,B,q);
            mul(M,M,B);
            //cout << M << endl;
            ind++;
        }

        if (M[1][0] != 0) {
            ZZ_pE temp;
            power(temp, M[0][0], q);
            rvals[i] = M[0][0] + temp;
            power(temp, M[1][0], q);
            rvals[i] += beta*temp;
        }
        else {
            operator_eval(bei, b, ei[i], p);
            rvals[i] = M[0][0] + bei*inv(M[0][0]);
        }


    }
    interpolate(interpol, ei, rvals);

    ZZ_pX res = to_ZZ_pX(0);
    for (long i = 0; i <= deg(interpol); i++)
        SetCoeff(res, i, coeff(coeff(interpol, i)._ZZ_pE__rep, 0));

    return res;

}

ZZ_pX gekeler(ZZ_pE& g, ZZ_pE& del, long p, long q_exp, int n, int m, ZZ_pX& P, ZZ_pE& inclusion) {

    int cnum = n/2 + 1, d = n/m;
    mat_ZZ_pE f;
    mat_ZZ_pE A;
    vec_ZZ_pE alphas;
    ZZ_pE det;
    alphas.SetLength(cnum);
    int q = pow(p, q_exp);
    vec_ZZ_pE x;
    x.SetLength(cnum);
    q = p;
    ZZ_pX Pn = power(P,m);
    ZZ_pX cons = ZZ_pX(INIT_MONO, 1, 1);
    ZZ_pE mono = conv<ZZ_pE>(cons);
    mono = inclusion;

    ZZ_pX b = pow(-1,n) * inv(norm(del)) * Pn;


    ZZ_pE temp;
    ZZ_pE temp2;
    ZZ_pE norm_delta_inv = inv(conv<ZZ_pE>(norm(del)));
    power(temp, del, pow(q,2*n));

    f.SetDims(2*n+1, 2*n+1);
    A.SetDims(cnum, cnum );
    f[0][0] = 1;
    //f[0][1] =
    f[1][0] = mono;
    f[1][1] = g;
    f[1][2] = del;


    for (int i = 2; i <= n; i++) {
        for (int j = 0; j < 2*i - 1; j++) {
            if (j == 0 ) {
                power(f[i][j], mono, i);
            }
            else if (j == 1) {
                power(temp, f[i-1][j-1], q);
                f[i][j] = mono*f[i-1][j] + g*temp;
            }
            else {
                power(temp, f[i-1][j-1], q);
                f[i][j] = mono*f[i-1][j] + g*temp;
                power(temp, f[i-1][j-2], q*q);
                f[i][j] += del*temp;
            }

        }
        power(temp, f[i-1][2*i-2], q);
        f[i][2*i-1] += g*temp;
        power(temp, f[i-1][2*i-3], q*q);
        f[i][2*i-1] += del*temp;


        power(temp, f[i-1][2*i-2], q*q);
        f[i][2*i] += del*temp;

    }

    if (n % 2 == 0) {
        alphas[cnum-1] = 1 + pow(-1,n)*norm_delta_inv*Pn[n]*f[n][2*n];
    }

    int end;
    if (n % 2 == 1) {
        end = cnum;
    }
    else end = cnum - 1;

    for (int j = 0; j < end; j++) {
        for(int i = ((2*j+n)/2); i <= n; i++  ) {
            alphas[j] += Pn[i]*f[i][2*j+n];
        }
        alphas[j] *= pow(-1,n)*norm_delta_inv;

    }

    for (int i = 0; i < cnum; i++) {
        for (int j = 0; j < cnum; j++) {
            A[j][i] = f[i][2*j];
        }
    }

    vec_ZZ_pE xx;
    xx.SetLength(cnum);

    solve(det, A, xx, alphas);

    ZZ_pX res = to_ZZ_pX(0);    
    for (long i = 0; i < xx.length(); i++)
        SetCoeff(res, i, coeff(xx[i]._ZZ_pE__rep, 0));

    return res;
}

//-------------------------------------------------
// finds frakp and gamma for parameters p, m, n
// REMARK: may be easier to start by setting frakp = a given irreducible polynomial in ZZ_p[x]
//         then make it a ZZ_pEX and let gamma be one of its roots in ZZ_pE
//-------------------------------------------------
void init(ZZ_pX& frakp, ZZ_pE& gamma, long p, int m, int n) {
    ZZ_p::init(ZZ(p));
    ZZ_pX P;
    BuildIrred(P, n);
    ZZ_pE::init(P);
    int d = n/m;
    clear(frakp);
    ZZ_pE alpha_char_rand;
    ZZ_p ref;

    if (m > 1) {
        while(deg(frakp) != d) {
            alpha_char_rand = random_ZZ_pE();
            ref = trace(alpha_char_rand);
            rtrace(gamma, alpha_char_rand, p, d, n);
            MinPolyMod(frakp, rep(gamma), ZZ_pE::modulus(), d);
        }
    } else {
        ZZ_pX cons = ZZ_pX(INIT_MONO, 1, 1);
        ZZ_pE mono = conv<ZZ_pE>(cons);
        frakp = P;
        gamma = mono;
    }

}

//-------------------------------------------------
// runs all test for p, n, m
// skips the deterministic algorithm if p is too small
//-------------------------------------------------
void run(int p, int n, int m) {

    ZZ_pX frakp;
    ZZ_pE gamma;
    init(frakp, gamma, p, m, n);

    ZZ_pE g, del;
    g = random_ZZ_pE();
    while( del == 0) 
        del = random_ZZ_pE();

    ZZ_pX out1, out2, out3;

    double start1, end1;
    start1 = GetTime();
    out1 = char_poly1(g, del, frakp, gamma);
    end1 = GetTime();
    cout << end1 - start1 << " ";
    
    if (n/2 + 1 < p) {
        start1 = GetTime();
        out2 = char_poly2(g, del, p, 1, n, m, frakp, gamma);
        end1 = GetTime();
        cout << end1 - start1 << " ";
    }
    else
    {
        out2 = to_ZZ_pX(0);
        cout << "0" << " ";
    }

    start1 = GetTime();
    out3 = gekeler(g, del, p, 1, n, m, frakp, gamma);
    end1 = GetTime();
    cout << end1 - start1 << endl;

#ifdef CHECK
    cout << "Char poly (rand): " << out1 << endl;
    cout << "Char poly (det): " << out2 << endl;
    cout << "Char poly (gekeler): " << out3 << endl;
#endif
}


int main() {

    if (1)
    {
        int p = 1009;
        int n = 50;
        int m = 1;
        run(p, n, m);
    }
    else
    {
        int times = 5;
        int pset[] {139, 269, 571, 1117, 2417, 5179, 16661, 39623, 104729, 212057, 431141, 1002527};
        int nset[] {1, 2, 4, 8, 16, 32, 42, 52, 64, 74, 84, 94, 104, 114, 128, 138, 148, 158, 256, 512, 1024, 2048, 4096, 8192};
        int len = 18;
        // ???
    }

}
