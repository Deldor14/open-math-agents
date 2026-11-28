P=polcompositum(polcyclo(11),x^3+x^2-2*x-1,1)[1]; G=nfinit(P[1]);xi=P[2]; th=P[3];lam=xi-1; lamid=idealhnf(G,lam);
ts=[th,th^2-2,1-th-th^2]; ys=vector(5,a,xi^a+xi^(-a)); gens=concat([[xi],ts,ys,vector(15,i,ys[(i-1)\3+1]-ts[(i-1)%3+1])]);
{for(i=1,#gens,if(abs(nfeltnorm(G,gens[i]))!=1,error("nonunit")));for(n=1,12,my(B=idealstar(G,idealpow(G,lamid,n),1,11),mat=Mat(apply(v->Mod(ideallog(G,v,B),11),gens)));print(n," ",matrank(mat)," ",#B.cyc));}
