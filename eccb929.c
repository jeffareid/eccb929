/*----------------------------------------------------------------------*/
/*      eccb929.c       ecc demo program                                */
/*                                                                      */
/*      (c) 2018 by Jeff Reid                                           */
/*----------------------------------------------------------------------*/
/* Permission is hereby granted, free of charge, to any person          */
/* obtaining a copy of this software and associated documentation files */
/* (the "Software"), to deal in the Software without restriction,       */
/* including without limitation the rights to use, copy, modify, merge, */
/* publish, distribute, sublicense, and/or sell copies of the Software, */
/* and to permit persons to whom the Software is furnished to do so,    */
/* subject to the following conditions:                                 */
/*                                                                      */
/* The above copyright notice and this permission notice shall be       */
/* included in all copies or substantial portions of the Software.      */
/*                                                                      */
/* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,      */
/* EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF   */
/* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND                */
/* NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS  */
/* BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN   */
/* ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN    */
/* CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE     */
/* SOFTWARE.                                                            */
/*----------------------------------------------------------------------*/
#define _CRT_SECURE_NO_WARNINGS 1       /* disable sscanf warnings */

#include <stdio.h>
#include <string.h>
#include <memory.h>

typedef unsigned char BYTE;

#define DISPLAYE 1                      /* display euclid stuff */
#define DISPLAYM 1                      /* display matrix stuff */
#define DISPLAYI 0                      /* display matrix inv */

/* galois field modulo GF */
#define GF 929
/* galois primitive */
#define ALPHA 3

/* max number of data */
#define MAXDAT 100

/* max number of parities */
#define MAXPAR 12

typedef struct{                         /* vector structure */
    int     size;
    int     data[GF];
}VECTOR;

typedef struct{                         /* euclid poly structure */
    int     size;                       /* # of data bytes */
    int     indx;                       /* index to right side */
    int     data[MAXPAR+2];             /* left and right side data */
}EUCLIDP;

typedef struct{                         /* matrix structure */
    int     nrows;
    int     ncols;
    int     data[(MAXPAR)*(MAXPAR)*2];
}MATRIX;

/*----------------------------------------------------------------------*/
/*      data                                                            */
/*                                                                      */
/*----------------------------------------------------------------------*/
static BYTE     abUser[80];
static int      aiExp[GF*2];
static int      aiLog[GF];

static VECTOR   vGenRoots;              /* generator roots */
static VECTOR   pGenPoly;               /* generator poly */
static VECTOR   vData;                  /* data */
static VECTOR   vErsf;                  /* erasure flags */
static VECTOR   vParities;              /* parities */
static VECTOR   vSyndromes;             /* syndromes */
static VECTOR   vErsLocators;           /* erasure locators */
static VECTOR   pErasures;              /* erasure poly */
static VECTOR   vModSyndromes;          /* modified syndromes */
static MATRIX   mModSyndromes;          /* mod syndrome matrix */
static VECTOR   pErrors;                /* reversed error locator poly */
static VECTOR   vErrLocators;           /* error locators */
static VECTOR   vLocators;              /* erasure + error locators */
static VECTOR   pLocators;              /* locator poly */
static MATRIX   mLocators;              /* locator matrix */
static MATRIX   mInvLoc;                /* inverse locator matrix */
static MATRIX   mModLocators;           /* Matrix of modified Locators */
static VECTOR   vErrValues;             /* error values */
static VECTOR   vInvLocators;           /* inverse (1/x) locators */
static VECTOR   vLocations;             /* locations n-1 to 0 */
static VECTOR   vOffsets;               /* offsets 0 to n-1 */

static EUCLIDP  E0;                     /* used by GenpErrorsE */
static EUCLIDP  E1;

static VECTOR   vB;                     /* used by GenpErrorsB */
static VECTOR   vC;
static VECTOR   vT;
static VECTOR   vBx;

static VECTOR   pLambda;                /* error locator poly */
static VECTOR   pDLambda;               /* derivative of pLambda */
static VECTOR   pOmega;                 /* error value poly */
static VECTOR   vForney;                /* errors values via Forney */

static MATRIX   mAltInvLoc;             /* alt inv loc matrix */
static VECTOR   vAltErrValues;          /* alt err values */

static int      abId[MAXPAR*2+1];       /* array for MatrixInv */

static int      iNumData;               /* number data - parities */

/*----------------------------------------------------------------------*/
/*      code                                                            */
/*----------------------------------------------------------------------*/
static void     Encode(void);
static void     Decode(void);
static void     GenSyndromes(void);
static int      GenErasures(void);
static void     GenModSyndromes(void);
static void     GenpErrorsM(void);
static void     GenpErrorsE(void);
static void     GenpErrorsB(void);
static void     MergeLocators(void);
static void     GenLambda(void);
static void     GenOffsets(void);
static void     GenmLocators(void);
static void     GenErrValues(void);
static void     GenAltInvLoc(void);
static void     GenOmega(void);
static void     GenForneyErr(void);
static void     FixvData(void);
static int      Poly2Root(VECTOR *, VECTOR *);
static void     Root2Poly(VECTOR *, VECTOR *);
static int      MatrixInv(MATRIX *, MATRIX *);
static int      GFAdd(int, int);
static int      GFSub(int, int);
static int      GFMpy(int, int);
static int      GFDiv(int, int);
static int      GFPow(int, int);
static void     InitGF(void);
static void     ShowEuclid(EUCLIDP *);
static void     ShowVector(VECTOR *);
static void     ShowMatrix(MATRIX *);
static int      Conrs(void);
static void     DoUser(void);

/*----------------------------------------------------------------------*/
/*      Encode                                                          */
/*----------------------------------------------------------------------*/
static void Encode(void)
{
int     iQuot;                          /* quotient */
int     iRem0, iRem1;                   /* partial remainders */
int     i, j;

    vParities.size = vGenRoots.size;    /* init vParities */
    memset(vParities.data, 0, vParities.size*sizeof(int));

    for(j = 0; j < iNumData; j++){      /* generate vParities */
        iQuot = GFAdd(vData.data[j], vParities.data[0]);
        iRem0 = 0;

        for(i = vGenRoots.size; i;){
            iRem1 = GFSub(iRem0, GFMpy(iQuot, pGenPoly.data[i]));
            i--;
            iRem0 = vParities.data[i];
            vParities.data[i] = iRem1;}}

    for(i = 0; i < vParities.size; i++){    /* append parities */
        vData.data[iNumData+i] = GFSub(0, vParities.data[i]);}
}

/*----------------------------------------------------------------------*/
/*      Decode                                                          */
/*----------------------------------------------------------------------*/
static void Decode(void)
{
    GenSyndromes();             /* generate syndromes */
    if(GenErasures())           /* generate erasure stuff */
        return;
    GenModSyndromes();          /* generate modified syndromes */
    GenpErrorsM();              /* generate error poly */
    GenpErrorsE();              /* generate error poly */
    GenpErrorsB();              /* generate error poly */
    printf("pLambda (B):    ");
    ShowVector(&vC);
    MergeLocators();            /* merge erasures + errors */
    printf("pLocators:      ");
    ShowVector(&pLocators);
    GenLambda();                /* generate lambda */
    printf("pLambda:        ");
    ShowVector(&pLambda);
    printf("pDLambda:       ");
    ShowVector(&pDLambda);
    GenOffsets();               /* generate offsets */
    GenmLocators();             /* generate locator matrix */
    MatrixInv(&mInvLoc, &mLocators); /* invert */
    GenErrValues();             /* generate error values */
    GenAltInvLoc();             /* generate alt matrix, err values */
    GenOmega();                 /* generate Omega */
    printf("pOmega:         ");
    ShowVector(&pOmega);
    GenForneyErr();             /* generate forney err values */

    printf("vLocators:      ");
    ShowVector(&vLocators);
    printf("vInvLocators:   ");
    ShowVector(&vInvLocators);
    printf("mInvLoc:\n");
    ShowMatrix(&mInvLoc);
    printf("mAltInvLoc:\n");
    ShowMatrix(&mAltInvLoc);
    printf("vErrValues:     ");
    ShowVector(&vErrValues);
    printf("vAltErrValues:  ");
    ShowVector(&vAltErrValues);
    printf("vForney:        ");
    ShowVector(&vForney);
    printf("vOffsets:       ");
    ShowVector(&vOffsets);
    FixvData();
}

/*----------------------------------------------------------------------*/
/*      GenSyndromes    generate standard RS syndromes                  */
/*----------------------------------------------------------------------*/
static void GenSyndromes(void)
{
int i,j;

    vSyndromes.size = vGenRoots.size;   /* set size */

    for(j = 0; j < vGenRoots.size; j++){
        vSyndromes.data[j] = vData.data[0]; /* generate a syndrome */
        for(i = 1; i < vData.size;  i++){
            vSyndromes.data[j] = GFAdd(vData.data[i],
                GFMpy(vGenRoots.data[j], vSyndromes.data[j]));}}

    printf("vSyndromes:     ");
    ShowVector(&vSyndromes);
}

/*----------------------------------------------------------------------*/
/*      GenErasures     generate vErsLocat...and pErasures              */
/*                                                                      */
/*      Scan vErsf right to left; for each non-zero flag byte,          */
/*      set vErsLocators to Alpha**power of corresponding location.     */
/*      Then convert these locators into a polynomial.                  */
/*----------------------------------------------------------------------*/
static int GenErasures(void)
{
int     iLcr;                           /* locator */
int     i, j;

    j = 0;                              /* j = index into vErs... */
    iLcr = 1;                           /* init locator */
    for(i = vErsf.size; i;){
        i--;
        if(vErsf.data[i]){              /* if byte flagged */
            vErsLocators.data[j] = iLcr; /*     set locator */
            j++;
            if(j > vGenRoots.size){      /*    exit if too many */
                return(1);}}
        iLcr = GFMpy(iLcr, ALPHA);}     /* bump locator */

    vErsLocators.size = j;              /* set size */

    Root2Poly(&pErasures, &vErsLocators); /* generate poly */

    return(0);
}

/*----------------------------------------------------------------------*/
/*      GenModSyndromes         Generate vModSyndromes                  */
/*                                                                      */
/*      First step in finding unknown locations.                        */
/*      Reset all unknown location parameters.                          */
/*      Each modified syndrome = sum(syndromes[i++]*perasures[j--]      */
/*----------------------------------------------------------------------*/
static void     GenModSyndromes(void)
{
int     iM;                             /* vModSyn.. index */
int     iS;                             /* vSyn.. index */
int     iP;                             /* pErs.. index */

    vModSyndromes.size = vSyndromes.size-vErsLocators.size;

    if(vErsLocators.size == 0){         /* if no erasures, copy */
        memcpy(vModSyndromes.data, vSyndromes.data, 
               vSyndromes.size*sizeof(int));
        goto genms0;}

    iS = 0;
    for(iM = 0; iM < vModSyndromes.size; iM++){ /* modify */
        vModSyndromes.data[iM] = 0;
        iP = pErasures.size;
        while(iP){
            iP--;
            vModSyndromes.data[iM] = GFAdd(vModSyndromes.data[iM],
                GFMpy(vSyndromes.data[iS], pErasures.data[iP]));
            iS++;}
        iS -= pErasures.size-1;}

genms0:
    printf("vModSyndromes:  ");
    for(iM = 0; iM < vGenRoots.size-vModSyndromes.size; iM++)
        printf("    ");
    ShowVector(&vModSyndromes);
    printf("pErasures:      ");
    ShowVector(&pErasures);
}

/*----------------------------------------------------------------------*/
/*      GenpErrorsM     generate pErrors via matrix algorithm           */
/*                                                                      */
/*      Generate augmented matrix from vModSyndromes                    */
/*      use gausian elimination (inversion)                             */
/*      If inversion fails, reduce error count (until 0) and repeat     */
/*      pErrors = inverted matrix times higher order vModSyndromes      */
/*----------------------------------------------------------------------*/
static void GenpErrorsM(void)
{
int     i, j, k, t;
int     *prowj;
int     *prowk;

    vErrLocators.size = vModSyndromes.size/2; /* init # errors */

    while(vErrLocators.size){           /* while # errors != 0 */
        mModSyndromes.nrows = vErrLocators.size;
        mModSyndromes.ncols = mModSyndromes.nrows+1;
        for(j = 0; j < mModSyndromes.nrows; j++){
            prowj = mModSyndromes.data+j*mModSyndromes.ncols;
            for(i = 0; i < mModSyndromes.nrows; i++){
                prowj[i] = vModSyndromes.data[i+j];}
            prowj[i] = GFSub(0, vModSyndromes.data[i+j]);}
#if DISPLAYM
        printf("mModSyndromes\n");
        ShowMatrix(&mModSyndromes);
#endif
    /* solve augmented matrix */
    for(k = 0; k < mModSyndromes.nrows; k++){
        prowk = mModSyndromes.data+k*mModSyndromes.ncols;
        for(j = k; j < mModSyndromes.nrows; j++)    /* find non-zero in column */
            if(mModSyndromes.data[j*mModSyndromes.ncols+k] != 0)
                break;
        if(j == mModSyndromes.nrows)                /* if redundant try 1 less error */
            goto gnp1;
        if(j != k){                                 /* swap rows if needed */
            prowj = mModSyndromes.data+j*mModSyndromes.ncols;
            for(i = 0; i < mModSyndromes.ncols; i++){
                t        = prowk[i];
                prowk[i] = prowj[i];
                prowj[i] = t;
            }
        }
        t = prowk[k];                               /* divide by M[k][k] */
        for(i = 0; i < mModSyndromes.ncols; i++)
            prowk[i] = GFDiv(prowk[i], t);
        for(j = 0; j < mModSyndromes.nrows; j++){   /* zero out columns */
            if(j == k)
                continue;
            prowj = mModSyndromes.data+j*mModSyndromes.ncols;
            t = prowj[k];
            for(i = 0; i < mModSyndromes.ncols; i++)
                prowj[i] = GFSub(prowj[i], GFMpy(prowk[i], t));
        }
    }

#if DISPLAYM
        printf("mModSyndromes\n");
        ShowMatrix(&mModSyndromes);
#endif

        /* copy to pErrors in reverse order */
        i = vErrLocators.size;
        pErrors.size = i+1;
        pErrors.data[0] = 1;
        for(j = 0; j < mModSyndromes.nrows; j++){
            prowj = mModSyndromes.data+j*mModSyndromes.ncols+mModSyndromes.ncols-1;
            pErrors.data[i--] = prowj[0];}
        if(Poly2Root(&vErrLocators, &pErrors)){ /* solve error poly */
gnp1:       vErrLocators.size--;                /* if fail try 1 less err */
            continue;}
        break;}

    if(!vErrLocators.size){             /* if no errors */
        pErrors.size = 1;               /*   handle no root case */
        pErrors.data[0] = 1;}

    printf("pErrors (M):    ");
    ShowVector(&pErrors);
}

/*----------------------------------------------------------------------*/
/*      GenpErrorsE     generate pErrors via Euclid division algorithm  */
/*----------------------------------------------------------------------*/
static void GenpErrorsE(void)
{
EUCLIDP *pED;                           /* PR[i-2] / PE[i-1] */
EUCLIDP *pER;                           /* PR[i-1] / PE[i-2] */
EUCLIDP *pET;                           /* temp */
int     iQuot;                          /* quotient */
int     iME;                            /* max errors possible */
int     i, j;

/*      left side of ED = PR[i-2], right side = reversed PE[i-1]        */
/*      left side of ER = PR[i-1], right side = reversed PE[i-2]        */

/*      E0 = initial ED */

    E0.size = vModSyndromes.size+2;        /* init rm[-2] / pe[-1] */
    E0.indx = vModSyndromes.size+1;
    E0.data[0] = 1;
    memset(&E0.data[1], 0, vModSyndromes.size*sizeof(int));
    E0.data[E0.indx] = 1;
    pED = &E0;

/*      E1 = initial ER */

    E1.size = vModSyndromes.size+2;        /* init rm[-1] / pe[-2] */
    E1.indx = vModSyndromes.size+1;
    E1.data[0] = 0;
    for(i = 1; i < E1.indx; i++){
        E1.data[i] = vModSyndromes.data[vModSyndromes.size-i];}
    E1.data[E1.indx] = 0;
    pER = &E1;

/*      init iME */

    iME = vModSyndromes.size/2;

/*      do Euclid algorithm */

    while(1){                           /* while size of PR[] > iME */
#if DISPLAYE
        printf("ED: ");
        ShowEuclid(pED);
        printf("ER: ");
        ShowEuclid(pER);
#endif
        while((pER->data[0] == 0) &&    /* shift dvsr left until msb!=0 */
              (pER->indx != 0)){        /*  or fully shifted left */
            pER->indx--;
            memcpy(&pER->data[0], &pER->data[1], (pER->size-1)*sizeof(int));
            pER->data[pER->size-1] = 0;}

        if(pER->indx <= iME){           /* if size of PR[] <= iME, stop */
            break;}

        while(1){                       /* while more divide sub-steps */
            if(pED->data[0]){           /*   if dvnd msb!=0, do quot */
                iQuot = GFDiv(pED->data[0], pER->data[0]);
                for(i = 0; i < pER->indx; i++){
                    pED->data[i] = GFSub(pED->data[i], GFMpy(iQuot, pER->data[i]));}
                for(i = pED->indx; i < pER->size; i++){
                    pER->data[i] = GFSub(pER->data[i], GFMpy(iQuot, pED->data[i]));}}
            if(pED->indx == pER->indx){ /*   if divide done, break */
                break;}
            pED->indx--;                /*   shift dvnd */
            memcpy(&pED->data[0], &pED->data[1], (pED->size-1)*sizeof(int));
            pED->data[pED->size-1] = 0;}

        pET = pER;                      /* swap dvnd, dvsr */
        pER = pED;
        pED = pET;}

    pErrors.size = pED->size-pED->indx; /* set pErrors.size */

    j = pErrors.size - 1;       /* right shift if leading zeroes */
    while(pER->indx < j){
        pER->indx++;
        for(i = pER->size-1; i;){
            i--;
            pER->data[i+1] = pER->data[i];}
        pER->data[0] = 0;}
#if DISPLAYE
    printf("EX: ");
    ShowEuclid(pER);
#endif

/*      pErrors = PE = non-reversed right side ED */

    if((pER->indx) >= pErrors.size){    /*  check remainder size */
        printf("GenpErrorsE remainder.size >= errors.size\n");
        goto fail0;}

    j = pED->indx;
    for(i = 0; i < pErrors.size; i++){
        pErrors.data[i] = pED->data[j];
        j++;}

#if DISPLAYE
    printf("pErrors (e):    ");
    ShowVector(&pErrors);
#endif

/*      Make most significant coef pErrors == 1 (divide by it) */

    iQuot = pErrors.data[0];
    if(iQuot == 0){
        printf("GenpErrorsE most sig coef of pErrors == 0\n");
        pLambda.size = 1;
        pLambda.data[0] = 1;
        goto fail0;}
    for(i = 0; i < pErrors.size; i++){
        pErrors.data[i] = GFDiv(pErrors.data[i], iQuot);}
    printf("pErrors (E):    ");
    ShowVector(&pErrors);

/*      if no erasures                                          */
/*      generate pOmega from ER (using iQuot = pErrors.data[0]) */

    if(vErsLocators.size == 0){
        pOmega.size = pER->indx;
        for(i = 0; i < pOmega.size; i++){
            pOmega.data[i] = pER->data[i];}
        printf("pOmega  (e):    ");
        ShowVector(&pOmega);
        for(i = 0; i < pOmega.size; i++){
            pOmega.data[i] = GFDiv(pER->data[i], iQuot);}
        printf("pOmega  (E):    ");
        ShowVector(&pOmega);}

/*      check poly with all syndromes */

    iQuot = 0;
    j = pErrors.size;
    while(j <= vModSyndromes.size){
        for(i = 0; i < pErrors.size; i++){
            j--;
            iQuot = GFAdd(iQuot, GFMpy(pErrors.data[i], vModSyndromes.data[j]));}
        if(iQuot != 0){
            printf("GenpErrorsE syndrome check detected error\n");
            goto fail0;}
        j += pErrors.size+1;}

/*      Find roots of pErrors (if fail, then set for no roots) */

    if(Poly2Root(&vErrLocators, &pErrors)){ /* solve error poly */
        printf("GenpErrorsE poly2root failed \n");
fail0:
        pErrors.size = 1;                   /* handle no root case */
        pErrors.data[0] = 1;
        pOmega.size = 0;
        vErrLocators.size = 0;}
}

/*----------------------------------------------------------------------*/
/*      GenpErrorsB     generate pErrors via Berklekamp Massey          */
/*      note poly most signifcant index == 0                            */
/*----------------------------------------------------------------------*/
static void GenpErrorsB(void)
{
int b, d, L, m;
int i, j, n;
int db;

    b = 1;                          /* discrepancy when L last updated */
    L = 0;                          /* number of errors */
    m = 1;                          /* # iterations since L last updated */
    vB.size    = 1;
    vB.data[0] = 1;
    vC.size    = 1;
    vC.data[0] = 1;

    for(n = 0; n < vModSyndromes.size; n++){
        d = vModSyndromes.data[n];     /* calculate discrepancy */
        for(i = 1; i <= L; i++){
            d = GFAdd(d, GFMpy(vC.data[(vC.size - 1)- i], vModSyndromes.data[n-i]));}
        if(d == 0){                 /* if 0 increment m, continue */
            m += 1;
            continue;}
        vT.size = vC.size;          /* vT = vC */
        memcpy(vT.data, vC.data, vC.size*sizeof(int));
        db = GFDiv(d,b);            /* db = (d/b) */
        vBx.size = vB.size+m;       /* Bx = x^m B */
        memcpy(vBx.data, vB.data, vB.size*sizeof(int));
        memset(&vBx.data[vB.size], 0, m*sizeof(int));
        for(i = 0; i < vBx.size; i++){ /* Bx *= db */
            vBx.data[i] = GFMpy(vBx.data[i], db);}
        j = vBx.size - vC.size;     /* right shift vBx or vC */
        if(j > 0){
            for(i = vBx.size; i > j; ){
                i--;
                vC.data[i] = vC.data[i-j];}
            memset(vC.data, 0, j*sizeof(int));
            vC.size += j;}
        else if(j < 0){
            j = -j;
            for(i = vC.size; i > j; ){
                i--;
                vBx.data[i] = vBx.data[i-j];}
            memset(vBx.data, 0, j*sizeof(int));
            vBx.size += j;}
        for(i = 0; i < vC.size; i++){ /* C -= Bx */
            vC.data[i] = GFSub(vC.data[i], vBx.data[i]);}
        if(n < 2*L){                /* if L not increasing */
            m += 1;
            continue;}
        vB.size = vT.size;          /*   B = T */
        memcpy(vB.data, vT.data, vT.size*sizeof(int));
        L = n + 1 - L;              /* update L */
        b = d;                      /* update b */
        m = 1;}                     /* reset m */
}

/*----------------------------------------------------------------------*/
/*      MergeLocators           merge ers and err locators              */
/*----------------------------------------------------------------------*/
static void MergeLocators(void)
{
int     iLcr;                           /* locator */
int     iLoc;                           /* location */
int     xErs;                           /* indexes */
int     xErr;
int     xLoc;

    vLocators.size   = vErsLocators.size+vErrLocators.size;
    vLocations.size  = vLocators.size;
    vOffsets.size    = vLocators.size;

    iLcr = 1;                           /* set up */
    iLoc = 0;

    for(xErs = xErr = xLoc = 0; xLoc < vLocators.size;){

        if(xErs < vErsLocators.size &&
          iLcr == vErsLocators.data[xErs]){
            vLocators.data[xLoc] = iLcr;
            vLocations.data[xLoc]  = iLoc;
            xLoc++;
            xErs++;}
        if(xErr < vErrLocators.size &&
          iLcr == vErrLocators.data[xErr]){
            vLocators.data[xLoc] = iLcr;
            vLocations.data[xLoc]  = iLoc;
            xLoc++;
            xErr++;}

        iLcr = GFMpy(iLcr, ALPHA);      /* try next locator */
        iLoc++;}

    for(xLoc = 0; xLoc < vLocators.size; xLoc++){
        vOffsets.data[xLoc] = vData.size-1-vLocations.data[xLoc];}

    Root2Poly(&pLocators, &vLocators);  /* generate poly */
}

/*----------------------------------------------------------------------*/
/*      GenLambda                                                       */
/*----------------------------------------------------------------------*/
static void GenLambda(void)
{
int i;
/*      pLambda = reverse of pLocators */

    pLambda.size = pLocators.size;
    for(i = 0; i < pLocators.size; i++){
        pLambda.data[i] = pLocators.data[(pLocators.size-1)-i];}

/*      generate vDLamda from pLambda */

    pDLambda.size = pLambda.size-1;
    for(i = 0; i < pLambda.size; i++){
        pDLambda.data[i] = GFMpy(pLambda.data[i], pDLambda.size - i);}
}

/*----------------------------------------------------------------------*/
/*      GenOffsets  vInvLocators, vLocations, vOffsets                  */
/*----------------------------------------------------------------------*/
static void GenOffsets(void)
{
int i;

    vInvLocators.size = vLocators.size;
    for(i = 0; i < vLocators.size; i++){
        vInvLocators.data[i] = GFDiv(1, vLocators.data[i]);}

    vLocations.size = vLocators.size;
    for(i = 0; i < vLocators.size; i++){
        vLocations.data[i] = aiLog[vLocators.data[i]];}

    vOffsets.size = vLocators.size;
    for(i = 0; i < vLocators.size; i++){
        vOffsets.data[i] = vData.size-1-vLocations.data[i];}
}

/*----------------------------------------------------------------------*/
/*      GenmLocators    Generate Locator matrix (for error values)      */
/*                                                                      */
/*      Matrix is composed of vGenRoots powered to vLocations.          */
/*      The inverse of this matrix is used to produce error values.     */
/*----------------------------------------------------------------------*/
static void GenmLocators(void)
{
int     *p0;                            /* ptr to matrix */
int     i, j;

    mLocators.nrows = vLocators.size;
    mLocators.ncols = vLocators.size;

    p0  = mLocators.data;               /* set up */

    for(j = 0; j < mLocators.nrows; j++){       /* do matrix */
        for(i = 0; i < mLocators.ncols; i++){
            *p0 = GFPow(vGenRoots.data[j],  vLocations.data[i]);
            p0++;}}
}

/*----------------------------------------------------------------------*/
/*      GenErrValues    generate error values                           */
/*                                                                      */
/*      Multiplying inverse locator matrix by the first few syndromes   */
/*      produces error values.                                          */
/*----------------------------------------------------------------------*/
static void GenErrValues(void)
{
int     iE;                             /* index to vErrValues */
int     iS;                             /* index to vSyndromes */
int     iI;                             /* index to imLocators */
int     i;

    iI = 0;
    vErrValues.size = mInvLoc.nrows;

    for(iE = 0; iE < vErrValues.size; iE++){
        vErrValues.data[iE] = 0;
        iS = 0;
        for(i = 0; i < mInvLoc.ncols; i++){
            vErrValues.data[iE] = GFAdd(vErrValues.data[iE],
                GFMpy(mInvLoc.data[iI], vSyndromes.data[iS]));
            iI++;
            iS++;}}
}

/*----------------------------------------------------------------------*/
/*      GenAltInvLoc    Generate alternate inverted locator matrix      */
/*                      and alternate error values                      */
/*                                                                      */
/*      Uses pLocators and vLocators to create imLocators equivalent    */
/*----------------------------------------------------------------------*/
static void GenAltInvLoc(void)
{
int     *pm;                            /* ptr to matrix */
int     i0, i1;                         /* temps */
int     i, j;

    mAltInvLoc.nrows = vLocators.size;
    mAltInvLoc.ncols = vLocators.size;
    vAltErrValues.size = vLocators.size;

    pm = mAltInvLoc.data;               /* set up */
    for(j = 0; j < mAltInvLoc.nrows; j++){

/*      Add a row: reversed poly divide (pLocators)/(1X - vLocators[j]) */
/*      This is equivalent to reversed order coefs of:                  */
/*      Root2Poly(row, vLocators with "jth" element dropped).           */

        pm += vLocators.size;
        i0 = 0;
        for(i = 0; i < mAltInvLoc.ncols; i++){
            *--pm = i0 = GFAdd(pLocators.data[i], GFMpy(i0, vLocators.data[j]));}

/*      i0 = sum of row[i]*Locator[j]**i = divisor for next step */

        i0 = 0;
        for(i = 0; i < mAltInvLoc.ncols; i++){
            i0 = GFAdd(i0, GFMpy(*pm, GFPow(vLocators.data[j],i)));
            pm++;}
        pm -= vLocators.size;

/*      adjust i0 for first root of vGenRoots */

        i0 = GFMpy(i0,GFPow(vGenRoots.data[0], vLocations.data[j]));

/*      divide the row by i0 */
/*      error value is summed up in i1. The 3 lines below       */
/*      using i1 are not needed for matrix generation.          */

        i1 = 0;
        for(i = 0; i < mAltInvLoc.ncols; i++){
            *pm = GFDiv(*pm, i0);
            i1 = GFAdd(i1, GFMpy(*pm, vSyndromes.data[i]));
            pm++;}
        vAltErrValues.data[j] = i1;
    }
}

/*----------------------------------------------------------------------*/
/*      GenOmega        generate Omega                                  */
/*----------------------------------------------------------------------*/
static void GenOmega(void)
{
int iO;                                 /* index to pOmega */
int iL;                                 /* index to pLambda */
int iS;                                 /* index to vSyndromes */
    pOmega.size = vLocators.size;
    for(iO = vLocators.size-1; iO >= 0; iO--){
        iS = vLocators.size-1-iO;
        pOmega.data[iO] = vSyndromes.data[iS--];
        for(iL = vLocators.size-1; iL > iO; iS, iL--){
            pOmega.data[iO] = GFAdd(pOmega.data[iO],
                    GFMpy(vSyndromes.data[iS--], pLambda.data[iL]));}}
}

/*----------------------------------------------------------------------*/
/*      GenForneyErr    generate error values using Forney              */
/*----------------------------------------------------------------------*/
static void GenForneyErr(void)
{
int i,j;
int iDvnd;
int iDvsr;

    vForney.size = pOmega.size;
    memset(vForney.data, 0, vForney.size*sizeof(int));
    for(j = 0; j < vForney.size; j++){
        iDvsr = iDvnd = 0;
        for(i = vForney.size; i;){
            i--;
            iDvnd = GFAdd(iDvnd, GFMpy(pOmega.data[i],
                    GFPow(vInvLocators.data[j], (vForney.size-1)-i)));
            iDvsr = GFAdd(iDvsr, GFMpy(pDLambda.data[i],
                    GFPow(vInvLocators.data[j], (vForney.size-1)-i)));}
        if(iDvsr == 0){
            printf("GenForneyErr divide by zero\n");
            vForney.size = 0;
            return;}
        vForney.data[j] = GFSub(0, GFDiv(iDvnd, iDvsr));}
}

/*----------------------------------------------------------------------*/
/*      FixvData        Fix up vData                                    */
/*----------------------------------------------------------------------*/
static void FixvData(void)
{
int i;

    for(i = 0; i < vOffsets.size; i++){
        vData.data[vOffsets.data[i]] = GFSub(
            vData.data[vOffsets.data[i]],
            vErrValues.data[i]);}
}

/*----------------------------------------------------------------------*/
/*      Poly2Root(pVDstx, pPSrc)        find roots of poly              */
/*----------------------------------------------------------------------*/
static int Poly2Root(VECTOR *pVDst, VECTOR *pPSrc)
{
int     iLcr;                           /* current locator */
int     iSum;                           /* current sum */
int     iV;                             /* index to pVDst */
int     i,j;

    pVDst->size = pPSrc->size-1;        /* set dest size */

    if(!pVDst->size)                    /* exit if null */
        return(0);

    iV   = 0;
    iLcr = 1;
    for(j = 0; j < vData.size;  j++){
        iSum = 0;                       /* sum up terms */
        for(i = 0; i < pPSrc->size; i++){
            iSum = GFMpy(iSum, iLcr);
            iSum = GFAdd(iSum, pPSrc->data[i]);}

        if(!iSum){                      /* if a root */
            if(iV == pVDst->size){      /*    exit if too many roots */
                return(1);}
            pVDst->data[iV] = iLcr;     /*    add locator */
            iV++;}

        iLcr = GFMpy(iLcr, ALPHA);}     /* set up next higher Alpha */

    if(iV != pVDst->size)               /* exit if not enough roots */
        return(1);

    return(0);
}

/*----------------------------------------------------------------------*/
/*      Root2Poly(pPDst, pVSrc)         convert roots into polynomial   */
/*----------------------------------------------------------------------*/
static void Root2Poly(VECTOR *pPDst, VECTOR *pVSrc)
{
int i, j;

    pPDst->size = pVSrc->size+1;
    pPDst->data[0] = 1;
    memset(&pPDst->data[1], 0, pVSrc->size*sizeof(int));
    for(j = 0; j < pVSrc->size; j++){
        for(i = j; i >= 0; i--){
            pPDst->data[i+1] = GFSub(pPDst->data[i+1],
                    GFMpy(pPDst->data[i], pVSrc->data[j]));}}
}

/*----------------------------------------------------------------------*/
/*      MatrixInv(pMDst, pMSrc) invert matrix                           */
/*      assumes square matrix                                           */
/*----------------------------------------------------------------------*/
static int MatrixInv(MATRIX *pMDst, MATRIX *pMSrc)
{
int     *p0;                            /* generic pointers */
int     *p1;
int     *p2;
int     iMod;                           /* row modifier */
int     iTemp;
int     iNCol;                          /* # columns */
int     iNCol2;                         /* 2 * # columns */
int     iNCol21;                        /* 1+2*# columns */
int     i, j;

    memset(abId, 0, sizeof(abId));      /* set up abId */
    abId[MAXPAR] =  1;

    iNCol   = pMSrc->ncols;             /* set size related stuff */
    iNCol2  = iNCol+iNCol;
    iNCol21 = iNCol2+1;

    pMDst->nrows = iNCol;               /* set destination size */
    pMDst->ncols = iNCol2;              /*   for display */

/*      generate double-width augmented matrix */
/*      left side is copy of pMSrc, right side is Identity Matrix */

    p0  = pMSrc->data;
    p1  = pMDst->data;
    for(i = 0; i < iNCol; i++){
        memcpy(p1,  p0, iNCol*sizeof(int)); /* copy a row of data */
        p0  += iNCol;
        p1  += iNCol;
        memcpy(p1,  &abId[MAXPAR-i], iNCol*sizeof(int)); /* add ID  part */
        p1  += iNCol;}

/*      normalize according to left side */
/*      results in inverse matrix in right size */

    #if DISPLAYI
        printf("start\n");
        ShowMatrix(pMDst);
    #endif

    for(j = 0; j < iNCol; j++){         /* working at [j][j] */

/*      find 1st non-zero in current column */

        p0  = pMDst->data+j*iNCol21;    /* p0 = starting ptr */
        p1  = p0;                       /* p1 = scanning ptr */
        p2  = pMDst->data+iNCol2*iNCol; /* p2 = end of  matrix */
        while(0 == *p1){
            p1  += iNCol2;
            if(p1 >= p2){               /* return if bad matrix */
                return(1);}}

        iMod = *p1;                 /* set divisor for row */

/*      swap rows if needed */

        if(p0 != p1){
            p0  -= j;                   /* backup to beg of rows */
            p1  -= j;
            for(p2  = p0+iNCol2; p0 != p2; p0++, p1++){
                iTemp = *p0;
                *p0 = *p1;
                *p1 = iTemp;}
            #if DISPLAYI
                printf("swapped rows\n");
                ShowMatrix(pMDst);
            #endif
            ;}


/*      divide row to produce a one */

        p0  = pMDst->data+j*iNCol2;     /* p0 = ptr to  start of row */
        for(p2  = p0+iNCol2; p0 != p2; p0++){
            *p0 = GFDiv(*p0, iMod);}

        #if DISPLAYI
            printf("divided row\n");
            ShowMatrix(pMDst);
        #endif

/*      subtract multiple of this row from other rows */
/*      to create a column of zeroes */
/*      (except for this row,column) */

        for(i = 0; i < iNCol; i++){
            if(i == j)                  /* skip if current row */
                continue;
            p0  = pMDst->data+j*iNCol2; /* p0 = ptr to  current row */
            p1  = pMDst->data+i*iNCol2; /* p1 = ptr to  target row */
            iMod = *(p1+j);         /* iMod = current row mpyr */
            for(p2  = p0+iNCol2; p0 != p2; p0++, p1++)
                *p1 = GFSub(*p1, GFMpy(*p0, iMod));}
#if DISPLAYI
        printf("zeroed columns\n");
        ShowMatrix(pMDst);
#endif
        ;}

/*      now copy right side of matrix to left side */

    p0  = pMDst->data;                  /* p0 = Dst ptr */
    p1  = p0+iNCol;
    for(j = 0; j < iNCol; j++){
        p2  = p0+iNCol;
        while(p0 != p2){
            *p0++ = *p1++;}
        p1  += iNCol;}

    pMDst->ncols = iNCol;               /* set proper ncols */
    return(0);
}

/*----------------------------------------------------------------------*/
/*      GFAdd(num0, num1)                                               */
/*----------------------------------------------------------------------*/
static int GFAdd(int num0, int num1)
{
int sum;
    sum = num0 + num1;
    if(sum >= GF)sum -= GF;
    return(sum);
}

/*----------------------------------------------------------------------*/
/*      GFSub(num0, num1)                                               */
/*----------------------------------------------------------------------*/
static int GFSub(int num0, int num1)
{
int dif;
    dif = num0 - num1;
    if(dif < 0)dif += GF;
    return(dif);
}

/*----------------------------------------------------------------------*/
/*      GFMpy(mpnd, mplr)                                               */
/*----------------------------------------------------------------------*/
static int GFMpy(int mpnd, int mplr)
{
    if((mpnd == 0) || (mplr == 0))
        return(0);
    return(aiExp[aiLog[mpnd] + aiLog[mplr]]);
}

/*----------------------------------------------------------------------*/
/*      GFDiv(dvnd, dvsr)                                               */
/*----------------------------------------------------------------------*/
static int GFDiv(int dvnd, int dvsr)
{
    if(dvsr == 0){
        printf("divide by zero\n");
        return(0);}
    if(dvnd == 0){
        return(0);}
    return(aiExp[(GF-1) + aiLog[dvnd] - aiLog[dvsr]]);
}

/*----------------------------------------------------------------------*/
/*      GFPow(mpnd, expn)                                               */
/*----------------------------------------------------------------------*/
static int GFPow(int mpnd, int expn)
{
int powr = 1;
    while(expn--)
        powr = GFMpy(powr, mpnd);
    return(powr);
}

/*----------------------------------------------------------------------*/
/*      InitGF  Initialize Galios Stuff                                 */
/*----------------------------------------------------------------------*/
static void InitGF(void)
{
int i;
int j;

    j = 1;                      /* init exp and log table */
    for(i = 0; i < GF-1; i++){
        aiExp[i] = j;
        aiLog[j] = i;
        j *= ALPHA;
        j %= GF;}
    aiLog[0] = -1;
    memcpy(&aiExp[GF-1], &aiExp[0], (GF-1)*sizeof(int));

    j = ALPHA;                  /* init generator poly */
    for(i = 0; i < vGenRoots.size; i++){
        vGenRoots.data[i] = j;
        j = GFMpy(j, ALPHA);}

    Root2Poly(&pGenPoly, &vGenRoots);
}

/*----------------------------------------------------------------------*/
/*      ShowEuclid
/*----------------------------------------------------------------------*/
static void ShowEuclid(EUCLIDP *pESrc)
{
int     i;
    for(i = 0; i < pESrc->indx; i++){
        printf(" %03d", pESrc->data[i]);}
    printf("|");
    for( ; i < pESrc->size; i++){
        printf("%03d ", pESrc->data[i]);}
    printf("\n");
}

/*----------------------------------------------------------------------*/
/*      ShowVector                                                      */
/*----------------------------------------------------------------------*/
static void ShowVector(VECTOR *pVSrc)
{
int     i;
    for(i = 0; i < pVSrc->size; i++){
        printf(" %03d", pVSrc->data[i]);
        if((i % 10) == 9){
            printf("\n");}}
    if((pVSrc->size == 0) || ((i % 10) != 0))
        printf("\n");
}

/*----------------------------------------------------------------------*/
/*      ShowMatrix                                                      */
/*----------------------------------------------------------------------*/
static void ShowMatrix(MATRIX *pMSrc)
{
int     iM;
int     i, j;
    iM = 0;
    for(i = 0; i < pMSrc->nrows; i++){
        for(j = 0; j < pMSrc->ncols; j++){
            printf(" %03d", pMSrc->data[iM++]);}
        printf("\n");}
}

/*----------------------------------------------------------------------*/
/*      Conrs  get console response - emulates _cgets()                 */
/*----------------------------------------------------------------------*/
static int Conrs(void)
{
int i;

    memset(abUser, 0, sizeof(abUser));  /* init abUser */
    abUser[0] = sizeof(abUser)-2;
    gets(&abUser[2]);                   /* get a line */
    abUser[1] = (BYTE)strlen(&abUser[2]);
    i = abUser[1];
    abUser[2+i] = 0;
    return(i);
}

/*----------------------------------------------------------------------*/
/*      main                                                            */
/*----------------------------------------------------------------------*/
int main()
{
    DoUser();
    return(0);
}

/*----------------------------------------------------------------------*/
/*      DoUser  do user stuff                                           */
/*----------------------------------------------------------------------*/
static void DoUser(void)
{
int i, j, k;

    printf("Ecc929 1.4\n");

    while(1){
        printf("Enter # of parities (1  -> %d):\n", MAXPAR);
        if(!Conrs())goto exit0;
        sscanf(&abUser[2], "%d", &i);
        if(i > 0 && i <= MAXPAR)break;}
    vGenRoots.size = i;
    j = MAXDAT-i;

    while(1){
        printf("Enter # of data (1 -> %d):\n", j);
        if(!Conrs())goto exit0;
        sscanf(&abUser[2], "%d", &i);
        if(i > 0 && i <= j)break;}

    iNumData = i;
    vData.size = i+vGenRoots.size;

    InitGF();

DoUser0:
    printf("vGenRoots:  ");
    ShowVector(&vGenRoots);
    printf("pGenPoly:   ");
    ShowVector(&pGenPoly);
    memset(vData.data, 0, vData.size*sizeof(int));

DoUser1:
    vErsf.size = vData.size;            /* reset vErsf */
    memset(vErsf.data, 0, vErsf.size*sizeof(int));

DoUser2:
    printf("vErsf:\n");
    ShowVector(&vErsf);
    printf("vData:\n");
    ShowVector(&vData);

    printf("Enter Change Ptr Zero Ncode Fix Quit: ");
    if(0 == Conrs())goto DoUser2;
    printf("\n");

    i = abUser[2] & 0x5f;

    switch(i){

      case 'E':                         /* enter data */
        for(i = 0; i < vData.size;  i++){
            printf("data[%03d] = ", i);
            if(!Conrs())break;
            sscanf(&abUser[2], "%d", &j);
            vData.data[i] = j;}
        break;
      case 'C':                         /* change data */
        k = 0;
DoUserc:
        while(1){
            printf("Enter offset (0 -> %d): ",  vData.size-1);
            if(!Conrs())break;
            sscanf(&abUser[2], "%d", &i);
            if(i >= vData.size)continue;
            printf("Enter value: (0 -> %d): ", (GF-1));
            if(!Conrs())break;
            sscanf(&abUser[2], "%d", &j);
            vData.data[i] = j;
            vErsf.data[i] = k;}
        break;
      case 'P':                         /* pointers */
        k = 1;
        goto DoUserc;

      case 'Z':                         /* zero data array */
        goto DoUser0;

      case 'N':                         /* encode ecc data */
        Encode();
        break;

      case 'F':                         /* fix data */
        Decode();
        goto DoUser1;

      case 'Q':                         /* quit */
        goto exit0;

      default:
        break;}

    goto DoUser2;

exit0:
    return;
}
