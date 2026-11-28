\\ The order-two subgroup fixes Q(zeta_7)^+ and zeta_11.
{my(v=subcyclopclgp([77,[34]],11,1));if(v[2][1] || v[3][1] || v[4]!=[30],error("class group"));print(v);my(w=subcyclopclgp(77,11,1));if(w[2][1] || w[3][1],error("ambient verification"));print(w);}
