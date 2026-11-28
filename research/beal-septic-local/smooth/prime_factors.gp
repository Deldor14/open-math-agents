\\ Independent list. No cyclotomic-polynomial factorization is assumed.
{my(S=List());forprime(r=2,100000,if(r==7,next);my(f=znorder(Mod(r,7)),F=factor(r^f-1));for(i=1,matsize(F)[1],if(F[i,1]>=11,listput(S,F[i,1]))));my(v=Set(Vec(S)));for(i=1,#v,print(v[i]));}
