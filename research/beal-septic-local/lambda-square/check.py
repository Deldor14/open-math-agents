"""Split-prime certificates for the second Fermat-quotient descent, using arithmetic modulo p^2."""
from pathlib import Path

root = Path(__file__).resolve().parent


def cubic_roots(p):
    roots = []
    for a in range(p):
        value = a**3 + a*a - 2*a - 1
        if value % p == 0:
            derivative = 3*a*a + 2*a - 2
            roots.append((a - value * pow(derivative, -1, p*p)) % (p*p))
    assert len(roots) == 3
    return roots


def data_at(p, theta, model):
    modulus = p*p
    d1, d2, d3 = 2-theta, 4-theta*theta, 1+theta+theta*theta
    if model == 0:
        T = (theta+2) % modulus
        W = 2*d2-d1
    else:
        T = (d2-d3)*pow(d2-d1, -1, modulus) % modulus
        W = 2*d3-d1-d2
    u = T*(T-1) % modulus
    qT = (pow(T,p-1,modulus)-1)//p
    qu = (pow(u,p-1,modulus)-1)//p
    y = (2*T-1) % p
    tangent = W*u*pow(y,-3,p)%p if y else 0
    return theta%p,T%p,qT,qu,tangent


def obstruction(p,t,qT):
    inv = [0,1]
    for i in range(2,p):
        inv.append((p-(p//i)*inv[p%i]%p)%p)
    first, second, power = 0,0,1
    for i in range(1,p):
        power = power*t%p
        first += power*inv[i]
        second += (power*inv[i]%p)*inv[i]
    return (2*second-qT*first)%p


def certify(p):
    roots = cubic_roots(p)
    for model in (0,1):
        places = [data_at(p,t,model) for t in roots]
        if any(not q for _,_,_,q,_ in places):
            continue
        minor = (places[0][2]*places[1][3] - places[1][2]*places[0][3])%p
        if not minor or not all(v[4] for v in places):
            continue
        for theta,t,qT,qu,trace in places:
            if qT and (ob := obstruction(p,t,qT)):
                return p,model,theta,t,qT,qu,minor,trace,ob
    return (p,)


if __name__ == '__main__':
    for p in map(int,(root/'exponents.txt').read_text().split()):
        print(*certify(p))
