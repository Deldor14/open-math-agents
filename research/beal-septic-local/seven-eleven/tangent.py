from residue import plus,product,times,power
p=11; z=(0,0,0); one=(1,0,0); th=(0,1,0); u=(2,3,1)
def c(n):return (n%11,0,0)
def add(a,b):return plus(a,b,11)
def mul(a,b):return product(a,b,11)
def sc(n,a):return times(n,a,11)
def pw(a,n):return power(a,n,11)
def div(a,b):assert b!=z;return mul(a,pw(b,1329))
def trace(a):return add(a,add(pw(a,11),pw(a,121)))
def solve(L,vals):
    m=[list(row)+[v] for row,v in zip(L,vals)]
    for j in range(5):
        i=next(i for i in range(j,5) if m[i][j]!=z);m[i],m[j]=m[j],m[i]
        lead=m[j][j];m[j]=[div(v,lead) for v in m[j]]
        for i in range(5):
            if i!=j:
                factor=m[i][j];m[i]=[add(a,sc(-1,mul(factor,b))) for a,b in zip(m[i],m[j])]
    return [row[-1] for row in m]
def test(start):
    rs=[];ys=[];ts=[]
    for i in range(start,1331+start):
        r=(i%11,i//11%11,i//121%11)
        a=add(one,sc(4,mul(u,pw(r,11))))
        if r!=z and pw(a,665)==one:
            for y in [pw(a,333)]:
                assert pw(y,2)==a
                T=sc(6,add(one,y))
                if T==z:continue
                rs.append(r);ys.append(y);ts.append(T)
        if len(rs)==5:break
    theta2=add(pw(th,2),c(-2));d1=add(c(2),sc(-1,th));d2=add(c(2),sc(-1,theta2));W=add(sc(-1,d1),sc(2,d2));Y0=add(sc(2,th),c(3))
    mat=[[div(pw(r,j),y) for r,y in zip(rs,ys)] for j in range(5)]
    target=[sc(j+1,div(W,Y0)) for j in range(5)]
    vs=solve(mat,target);jet=z
    for r,y,T,b in zip(rs,ys,ts,vs):
        jet=add(jet,mul(div(u,mul(y,T)),add(pw(b,11),sc(-1,mul(pw(r,10),b)))))
    return rs,jet,trace(jet)
if __name__=='__main__':
    for start in [1,92,307,602]:
        points, coefficient, value = test(start)
        assert value == (4,0,0)
        print('residues',points,'coefficient',coefficient,'trace',value)
