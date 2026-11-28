\\ Run from this directory in the public research tree.
{my(ex=Set(readvec("../mixed-seventh/exponents.txt")),n=0,d=0);
forprime(r=2,100000,
  my(f=if(r==7,1,znorder(Mod(r,7))), m=if(r==7,1,if(f%2,r^f-1,r^(f/2)+1)));
  my(ps=select(k->k>=11,factor(m)[,1]),kind=if(!#ps,1,if(#setminus(Set(Vec(ps)),ex)==0,2,0)));
  if(kind,print(r," ",if(kind==1,"local","descent"))); if(kind==1,n++); if(kind==2,d++)
)}
