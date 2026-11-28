/* Exact point counting on the three Frey models in their quadratic field.
   Input rows: p q f tr_minus tr_zero tr_plus, with traces modulo p over F_(q^f). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static const int coeff[3][4] = {
    {-2106,702,42120,-16497}, {-189,27,837,-270}, {-270,-162,-1188,-783}
};

static inline int mod(int64_t x, int q) {
    int r = x % q;
    return r < 0 ? r+q : r;
}

static int64_t count_trace(int q, int curve, int root, const signed char *chi) {
    const int *c = coeff[curve];
    int64_t sum = 0;
    if (root >= 0) {
        int a4 = mod(c[0] + (int64_t)c[1]*root,q);
        int a6 = mod(c[2] + (int64_t)c[3]*root,q);
        for (int64_t x=0; x<q; ++x)
            sum += chi[mod(x*(x*x+a4)+a6,q)];
    } else {
        /* x=a+b h, h^2=h+3. chi_2(t+u h)=chi_1(t^2+tu-3u^2). */
        for (int64_t b=0; b<q; ++b) {
            int64_t b2 = b*b;
            for (int64_t a=0; a<q; ++a) {
                int64_t v = a*a+3*b2+c[0], w=2*a*b+b2+c[1];
                int64_t t = mod(a*v+3*b*w+c[2],q);
                int64_t u = mod(a*w+b*v+b*w+c[3],q);
                sum += chi[mod(t*t+t*u-3*u*u,q)];
            }
        }
    }
    return -sum;
}

static int extends_to(int64_t trace, int q, int degree, int extension,
                      int p, int target) {
    if (extension % degree) return 0;
    int Q = mod(degree==1 ? q : (int64_t)q*q,p);
    int previous=2, current=mod(trace,p);
    for (int i=1; i<extension/degree; ++i) {
        int next=mod(trace*current-(int64_t)Q*previous,p);
        previous=current;
        current=next;
    }
    return current==target;
}

int main(void) {
    int p,q,f,target[3],rows=0;
    while (scanf("%d %d %d %d %d %d",&p,&q,&f,&target[0],&target[1],&target[2])==6) {
        if (q<3 || q>20000 || p<5 || f<1 || f>12) return 1;
        signed char *chi=malloc(q);
        if (!chi) return 1;
        for (int i=1; i<q; ++i) chi[i]=-1;
        chi[0]=0;
        for (int64_t i=1; i<q; ++i) chi[(i*i)%q]=1;
        int roots[2]={-1,-1}, count=0;
        for (int64_t x=0; x<q; ++x)
            if (mod(x*x-x-3,q)==0) roots[count++]=(int)x;
        int matched=0;
        for (int i=0; i<(count ? count : 1); ++i) {
            int64_t t[3];
            int ok=1;
            for (int j=0; j<3; ++j) {
                t[j]=count_trace(q,j,roots[i],chi);
                ok &= extends_to(t[j],q,count ? 1 : 2,f,p,target[j]);
            }
            if (ok) {
                printf("%d %d %lld %lld %lld\n",p,q,(long long)t[0],
                       (long long)t[1],(long long)t[2]);
                matched=1;
                break;
            }
        }
        free(chi);
        if (!matched || target[0]==target[1] || target[0]==target[2]) return 1;
        ++rows;
    }
    return rows==18 ? 0 : 1;
}
