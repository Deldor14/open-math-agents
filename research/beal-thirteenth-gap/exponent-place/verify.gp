vcoeff(a)=Col(Vecrev(liftint(lift(a)),12));
\\ Necessity: alpha/bar(alpha) is a pth power, Norm(alpha) a rational pth power.
entry(p)={my(F=Mod(1,p^2)*polcyclo(13),z=Mod(Mod(1,p^2)*x,F),w=z^-1,fz=z^p,fw=w^p,accept=List(),angles=0);
for(t=0,p-1,
  my(A=(t+(1-t)*z)^p,B=(t+(1-t)*w)^p);
  my(c=vcoeff(A*(t+(1-t)*fw)-B*(t+(1-t)*fz)),s=vcoeff(A*(1-fw)-B*(1-fz))*Mod(1,p));
  if(c*Mod(1,p)!=0,error("Frobenius"));
  my(C=c/p*Mod(1,p),j=1);while(j<=12 && s[j]==0,j++);
  if(j>12,error("zero slope"));
  my(k=-C[j]/s[j]);if(C+k*s!=0,next);
  angles++;
  my(T=t+p*lift(k),n=Mod(T,p^2)^13+(1-Mod(T,p^2))^13);
  if(n==0 || n^(p-1)==1,listput(accept,T)));
if(angles!=3,error("unexpected angle count"));vecsort(Vec(accept))};
C=[[-2106,702,42120,-16497],[-189,27,837,-270],[-270,-162,-1188,-783]];
frob(p)={my(fs=factor(Mod(1,p)*(x^2-x-3)),V=vector(matsize(fs)[1],i,my(h=ffgen(fs[i,1],'h));vector(3,j,my(c=C[j],E=ellinit([c[1]+c[2]*h,c[3]+c[4]*h],h));if(E==[],error("bad curve"));ellap(E))));return(V)};
units(Z)={my(w=Z+Z^-1);[w,w^2-1,w^3-2*w,w^4-3*w^2+1,w^5-4*w^3+3*w]};
ket(p)={my(Z=Mod(Mod(1,p^2)*x,Mod(1,p^2)*polcyclo(13)),n=p^12-1,U=units(Z),B=matconcat(apply(u->Col(Vecrev(liftint(lift(u^n-1))/p,12))*Mod(1,p),U)));lift(matker(B))};
sift(p,q,col)={my(f=znorder(Mod(q,13)));if(f==1 || (q^f-1)%p,return([]));my(Z=Mod(Mod(1,q)*x,Mod(1,q)*polcyclo(13)),e=(q^f-1)/p,U=units(Z),k=prod(i=1,5,U[i]^col[i])^e);if(k==1,return([]));my(M=Map(),A=List(),v=k^0);for(i=0,p-1,mapput(M,v,i);v*=k);for(t=0,q-1,my(j);if(mapisdefined(M,(t+(1-t)*Z)^e,&j),listput(A,j)));my(I=(1-Z)^e);for(j=0,p-1,my(v=lift(I/k^j));if(poldegree(v)<=0 && (q-1)%p==0 || v==1,listput(A,j)));return(Set(Vec(A)))};
aux(p,q)={my(f=znorder(Mod(q,13)));if(f==1 || (q^f-1)%p,return(0));my(Fq=polcyclo(13)*Mod(1,q),Z=Mod(Mod(1,q)*x,Fq),k=lift(-1/Mod(12,p)),v=((1-Z)^12/13)^k,e=(q^f-1)/p);for(t=0,q-1,if(((t+(1-t)*Z)*v)^e==1,return(0)));my(z=ffgen(factor(Fq)[1,1],'r),A1=z+z^-1,A3=z^3+z^-3,A4=z^4+z^-4,T=vector(3,i,my(b=i-2,A=(A4-A3)*(1+A1*b+b^2),B=(A1-A4)*(1+A3*b+b^2));ellap(ellinit([0,B-A,0,-A*B,0],z))));if((T[1]-T[2])%p && (T[1]-T[3])%p,return([q,f,T]));0};
other(p,q)={my(f=znorder(Mod(q,13)));if(f==1 || (q^f-1)%p,return(0));my(Fq=polcyclo(13)*Mod(1,q),Z=Mod(Mod(1,q)*x,Fq),v=1/(1+Z),e=(q^f-1)/p);for(t=0,q-1,if(((t+(1-t)*Z)*v)^e==1,return(0)));if(poldegree(lift(((1-Z)*v)^e))>0,return([q,f]));0};
basis()={my(F=x^6+x^5-5*x^4-4*x^3+6*x^2+3*x-1,H=bnfinit(F,1),w=Mod(x,F),u=[w,w^2-1,w^3-2*w,w^4-3*w^2+1,w^5-4*w^3+3*w]);my(B=matconcat(apply(e->vecextract(bnfisunit(H,e),"1..5"),u)));if(!bnfcertify(H) || H.no!=1 || abs(matdet(B))!=1,error("real units"))};
finite()={my(total=0);forprime(p=5,5000,if(p==13,next);total++;
  my(a=entry(p),wanted=if(p==1093 || p==3511,[0,1,(p^2+1)/2],[0,1]));
  if(a!=wanted,error("finite chart ",p));
  my(V=frob(p),e0=0,e1=0);for(i=1,#V,if((V[i][1]-V[i][2])%p,e0=1);if((V[i][1]-V[i][3])%p,e1=1));
  if((e0*e1==0)!=(p==3067),error("p-traces ",p));
  my(K=ket(p),kdim=matsize(K)[2]);
  if(kdim!=(p==151 || p==241),error("kernel ",p));
  if(p==151,if(sift(p,269,K[,1])!=[0],error("151")));
  if(p==241,if(setintersect(sift(p,1447,K[,1]),sift(p,4337,K[,1]))!=[0],error("241"))));
  if(total!=666,error("count"));print("finite chart, Frey traces and unit kernels: ",total," primes")};
extras()={my(v=aux(3067,12269));if(!v,error("3067 branch"));print("3067 auxiliary ",v);
  if(!other(1093,4373) || !other(3511,77243),error("Wieferich branch"));
  if(Mod(2,1093^2)^1092!=1 || Mod(2,3511^2)^3510!=1,error("base 2"));print("Wieferich alternatives excluded")};
iferr(basis();finite();extras(),exc,print(exc);quit(1));quit
