F=x^6+x^5-5*x^4-4*x^3+6*x^2+3*x-1;
S=[71,89,113,137,167,179,191,227,251,269,383,503,509,641,643,661,743,947];
\\ Constant-first vectors of residues in the thirteenth cyclotomic quotient.
coords(v,p)=Col(Vecrev(liftint(lift(v)),12))*Mod(1,p);
jet(v,p,n)=coords(Mod(liftint(lift(v^n-1))/p,polcyclo(13)),p);
first(p)={my(m=p^2,F2=Mod(1,m)*polcyclo(13),Z=Mod(Mod(1,m)*x,F2),Zp=Mod(Mod(1,p)*x,polcyclo(13)*Mod(1,p)),w=Z+Z^-1,n=p^12-1,units=[w,w^2-1,w^3-2*w,w^4-3*w^2+1,w^5-4*w^3+3*w],B=matconcat(apply(u->jet(u,p,n),units)),accept=List());if(matrank(B)!=5,error("unit kernel"));for(t=0,p-1,my(X=t+(1-t)*Z,V=coords((1-Zp)/(t+(1-t)*Zp),p),A=matconcat([B,V]),c=matinverseimage(A,jet(X,p,n)));if(matrank(A)!=6,error("direction"));if(#c,listput(accept,[t+p*lift(c[6]),lift(c[1..5])])));return(Vec(accept))};
units()={my(H=bnfinit(F,1),t=Mod(x,F),a=1,b=t,ls=List());for(i=2,6,listput(ls,b);my(c=t*b-a);a=b;b=c);my(B=matconcat(apply(u->vecextract(bnfisunit(H,u),"1..5"),Vec(ls))));if(!bnfcertify(H) || H.no!=1 || abs(matdet(B))!=1,error("unit or class basis"))};
boundary(p)={
  my(z=Mod(Mod(1,p^2)*x,Mod(1,p^2)*polcyclo(13)),ord=znorder(Mod(p,13)),f=if(ord%2,ord,ord/2),N=1,T=0,expn=p*(p^12-1));
  for(j=0,f-1,
    my(v=z^(lift(Mod(p,13)^j)),v1=v^p,t=if(p==71,v^6+v^-6,v+v^-1),t1=if(p==71,v1^6+v1^-6,v1+v1^-1));
    my(U=if(p==71,-(t+1)*(t+2)^(expn-2),(t+1)*(t+2)),Y=if(p==71,-t*(t+2)^(expn-1),2*t+3),WF=if(p==71,t1*(t1-2),6+t1-2*t1^2));
    N*=U;T+=WF*U*Y^(expn-3));
  if(Mod(1,p)*liftint(lift(T))==0,error("all local traces vanish"));
  if(f==3,my(Q=liftint(lift(N^(p-1)-1))/p*Mod(1,p));if(poldegree(gcd(Q,Mod(1,p)*polcyclo(13)))!=0,error("a norm digit vanishes")))
};
main()={units();for(i=1,#S,my(p=S[i],v=first(p));if(#v!=2 || v[1][1]!=0 || v[2][1]!=1 || v[1][2]!=0 || v[2][2]!=0,error("unit sieve"));boundary(p);print("passed ",p))};
iferr(main(),exc,print(exc);quit(1));quit
