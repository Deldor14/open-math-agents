\\ Independent lift of five divisors and their Kummer value in the ray group.
P=polcompositum(polcyclo(11),x^3+x^2-2*x-1,1)[1]; G=nfinit(P[1]); xi=P[2]; th=P[3]; lam=xi-1; lamid=idealhnf(G,lam); pr=nfmodprinit(G,idealprimedec(G,11)[1],'t); u=(th+1)*(th+2);
red(a)=nfmodpr(G,a,pr);
represent(a)=nfbasistoalg(G,nfmodprlift(G,a,pr));
yroot(X,res)={my(v=1+4*u*X^11,y=represent(res));for(i=1,11,y+=lam^i*represent(red((v-y^2)/lam^i)/(2*res)));if(nfeltval(G,v-y^2,pr[3])<12,error("Hensel"));y};
rs=[1,2,-1,th,1+th]; ys=apply(a->red(1+4*u*a^11)^333,rs); rr=apply(red,rs); mat=matrix(5,5,i,j,rr[j]^(i-1)/ys[j]); W=red(6+th-2*th^2); Y0=red(2*th+3); v=matsolve(mat,Col(vector(5,i,i*W/Y0)));
{my(Km=1);for(i=1,5,my(y=yroot(rs[i],ys[i]),yp=yroot(rs[i]+lam*represent(v[i]),ys[i]));Km*=(1+yp)/(1+y));my(jet=red((Km-1)/lam^11));print("Kummer valuation ",nfeltval(G,Km-1,pr[3])," trace ",lift(trace(jet)));if(lift(trace(jet))!=4,error("boundary trace"));for(n=11,12,my(B=idealstar(G,idealpow(G,lamid,n),1,11),vlog=lift(Mod(ideallog(G,Km,B),11)));print("Kummer image nontrivial at depth ",n," = ",vlog!=0);if((vlog!=0)!=(n==12),error("ray check")));}
