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
  if(n^(p-1)==1,listput(accept,T)));
if(vecsort(Vec(accept))!=[0,1],error("unresolved entry"));angles};

rows=[[71, 569], [89, 179], [113, 1583], [137, 823], [167, 1669], [179, 359], [191, 2293], [227, 7717], [251, 503], [269, 2153], [383, 4597], [503, 3019], [509, 1019], [641, 1283], [643, 6607], [661, 1321], [743, 1487], [947, 13259]];
F=y^6+y^5-5*y^4-4*y^3+6*y^2+3*y-1;
auxiliary(p,q)={
  my(f=znorder(Mod(q,13)),A=polcyclo(13)*Mod(1,q),z=Mod(Mod(1,q)*x,A));
  if(!isprime(q) || f<=1 || (q^f-1)%p,error("auxiliary prime"));
  my(k=lift(-1/Mod(12,p)),m=((1-z)^12/13)^k,e=(q^f-1)/p);
  for(t=0,q-1,if(((t+(1-t)*z)*m)^e==1,error("extraneous finite residue")));
  my(r=ffgen(factor(A)[1,1],'r),v=r+r^-1,w=r^3+r^-3,t=r^4+r^-4);
  my(tr=vector(3,i,my(b=i-2,E=(t-w)*(1+v*b+b^2),G=(v-t)*(1+w*b+b^2));ellap(ellinit([0,G-E,0,-E*G,0],r))));
  if((tr[1]-tr[2])%p==0 || (tr[1]-tr[3])%p==0,error("Frey traces"));lift(Mod(tr,p))
};
arithmetic(p)={
  my(h=lift(chinese(Mod(-1,13),Mod(1,p))),group=subcyclopclgp([13*p,[h]],p,1));
  if(group[2][1] || group[3][1],error("class group"));
  my(fs=factorpadic(F,p,3),count=matsize(fs)[1]);
  if(count>2,error("more than two places"));
  my(out=vector(count,i,
    my(phi=liftall(fs[i,1])*Mod(1,p^2),t=Mod(Mod(1,p^2)*y,phi),r=ffgen(lift(phi)*Mod(1,p),'r),f=poldegree(phi));
    my(u=if(p==71,-(t+1)/(t+2)^2,(t+1)*(t+2)),U=if(p==71,-(r+1)/(r+2)^2,(r+1)*(r+2)));
    my(Y=if(p==71,-r/(r+2),2*r+3),W=if(p==71,r*(r-2),6+r-2*r^2));
    [lift(norm(u)^(p-1)-1)/p,lift(trace(W*(U/Y^3)^(p^(f-1))))]));
  if(count==2 && (out[1][1]==0 || (out[1][1]+out[2][1])%p),error("torsion synchronization"));
  if(!vecsum(apply(v->v[2],out)),error("boundary traces"));out
};
main()={for(i=1,#rows,my(p=rows[i][1],q=rows[i][2]);if(!isprime(p),error("not prime"));my(angles=entry(p),tr=auxiliary(p,q),out=arithmetic(p));print([p,q,angles,tr,out]))};
iferr(main(),exc,print(exc);quit(1));
quit
