

#include <iostream>
#include <NTL/ZZ_pX.h>
#include <NTL/matrix.h>
#include <NTL/ZZ_pXFactoring.h>
#include <NTL/ZZ_pE.h>
#include <NTL/ZZ_pEX.h>
#include <NTL/ZZX.h>

#include "BaseChange.h"
#include "MultipointEval.h"
#include "Util.h"
#include "HasseLift.h"
#include "HasseLiftExt.h"
#include "MultiComposeMod.h"
#include "FrobComp.h"

using namespace std;

void testHasseLift(long p, long n) {

    ZZ_p::init(to_ZZ(p));
    ZZ_pX f, g, delta, lift;
    BuildIrred(f, n);
    ZZ_pXModulus F;
    build(F, f);

    random(g, n);
    random(delta, n);

    HasseLiftExt hasseLiftExt(g, delta, F);

    double start = GetWallTime();
    hasseLiftExt.compute(lift, n, 0);
    cout << GetWallTime() - start << endl;
}

int main(int argc, char** argv) {

    long p = 7;
    long n = 100;

    testHasseLift(p, n);
    
    return 0;
}

