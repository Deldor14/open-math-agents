p=41;q=163;F=polcyclo(13)*Mod(1,q);z=ffgen(F,'r);
qcheck()={if(znorder(Mod(q,13))!=12 || !polisirreducible(F),error("residue degree"));my(k=lift(-1/Mod(12,p)),mu=(13/(1-z)^12)^k,e=(q^12-1)/p,ts=select(t->((t+(1-t)*z)/mu)^e==1,[0..q-1]));if(#ts,error("extraneous candidate"));print("extraneous finite candidates ",ts)};
shortmodel(b)={my(v=z+z^-1,w=z^3+z^-3,t=z^4+z^-4,A=(t-w)*(1+b*v+b^2),B=(v-t)*(1+b*w+b^2),C=-A-B);[27*(A*B+A*C+B*C),-27*(2*A^3+3*A^2*B-3*A*B^2-2*B^3)]};
models()={my(h=1+z+z^-1+z^3+z^-3+z^4+z^-4,v=ffgen(Mod(1,q)*(x^2-x-3),'v),coeffs=[[13,50,66,129],[137,27,22,56],[56,1,116,32]],tr=vector(3),ext=vector(3));if(h^2!=h+3,error("quadratic basis"));for(i=1,3,my(co=coeffs[i],E=shortmodel(i-2));if(E!=[co[1]+co[2]*h,co[3]+co[4]*h],error("model coefficients"));tr[i]=ellap(ellinit([co[1]+co[2]*v,co[3]+co[4]*v],v));ext[i]=ellap(ellinit(E,z)));print("quadratic traces ",tr,"; degree-12 residues ",lift(Mod(ext,p)));if((tr[1]-tr[2])%p==0 || (tr[1]-tr[3])%p==0 || lift(Mod(ext,p))!=[30,3,0],error("modular comparison"))};
iferr(qcheck();models(),err,print(err);quit(1));
quit
