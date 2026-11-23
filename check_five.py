"""Reconstruct real endpoints of five-row complex Hardy frames and check their Born scores."""
from itertools import combinations
from fractions import Fraction as Q

import numpy as np
from scipy.optimize import minimize

# These reference routines come from the project's four-level Born reconstruction
# and graph-chart checker. They are included here for standalone replay.
RHO = 1.32471795724474602596
P_STAR = (8 * RHO**2 + RHO - 11) / 25


def basis(x):
    return np.linalg.qr(x, mode="reduced")[0]


def complement(x):
    return np.linalg.qr(x, mode="complete")[0][:, x.shape[1]:]


def probability(a, d, b):
    """The Bob subspace has already been conjugated in the Schmidt basis."""
    return np.linalg.norm(a.conj().T @ (d[:, None] * b), "fro") ** 2


def score(d, u):
    u = basis(u)
    v = complement(d[:, None]**5 * u)
    return probability(u, d, v)


def pair_error(x, y):
    return abs(x*y**5 - y*x**5) / (x**5 + y**5)


def maximal_chain(d, u):
    """Start at A0=D²U. Each space has orthonormal columns."""
    col = d[:, None]
    a0 = basis(col**2 * u)
    b0 = complement(col * a0)
    a1, b1 = basis(b0 / col), basis(a0 / col)
    a2, b2 = basis(b1 / col), basis(a1 / col)
    forbidden = [probability(a0, d, b0),
                 probability(a1, d, complement(b0)),
                 probability(complement(a0), d, b1),
                 probability(a2, d, complement(b1)),
                 probability(complement(a1), d, b2)]
    return max(forbidden), probability(a2, d, b2)


def chart_objective(x, n, rank):
    """Negative trace residual and its analytic gradient in a complex graph chart."""
    m = (n-rank)*rank
    d = np.exp(np.r_[0., x[:n-1]])
    b = (x[n-1:n-1+m] + 1j*x[n-1+m:]).reshape(n-rank, rank)
    u = np.vstack([np.eye(rank), b])
    h_inv = np.linalg.inv(u.conj().T @ u)
    image = d[:, None]**5*u
    target = d[:, None]*u
    # QR least squares avoids forming the condition-number-squaring normal equations.
    coeff = np.linalg.lstsq(image, target, rcond=None)[0]
    residual = target-image@coeff
    e = residual@h_inv
    raw = np.vdot(residual, e).real
    norm2 = np.dot(d, d)
    f = raw/norm2
    y = e@coeff.conj().T
    du = 2*(d[:, None]*e - d[:, None]**5*y - u@h_inv@(residual.conj().T@e))/norm2
    dd = 2*np.real(np.sum(u.conj()*(e-5*d[:, None]**4*y), axis=1))
    dlog = (d*dd-2*d**2*f)/norm2
    g = np.r_[dlog[1:], du[rank:].real.ravel(), du[rank:].imag.ravel()]
    return -f, -g

def bloch(x):
    a, b = x.T
    cross = a.conjugate() * b
    return np.column_stack((2*cross.real, 2*cross.imag, abs(a)**2-abs(b)**2))

def planar_frame(p, points):
    """Real qubit rows with the supplied lengths and coplanar Bloch vectors."""
    _, _, vh = np.linalg.svd(points, full_matrices=False)
    x, z = (points @ vh[:2].T).T
    angle = np.arctan2(x, z)/2
    return np.sqrt(p)[:,None] * np.column_stack((np.cos(angle), np.sin(angle)))

def endpoints(x):
    p = (abs(x)**2).sum(axis=1)
    v = bloch(x)
    if np.linalg.matrix_rank(v, tol=1e-11) <= 2:
        y = planar_frame(p, v)
        return y, y, 0.5
    a, b, c = v.T
    equations = np.column_stack((a*a, b*b, c*c, 2*a*b, 2*a*c, 2*b*c))
    _, _, vh = np.linalg.svd(equations, full_matrices=True)
    a, b, c, f, g, h = vh[-1]
    form = np.array([[a,f,g],[f,b,h],[g,h,c]])
    lam, coords = np.linalg.eigh(form)
    low, high = lam[0], lam[-1]
    assert low < 0 < high
    def make(edge):
        scales = np.sqrt(np.clip(1-lam/edge, 0, None))
        return planar_frame(p, (v @ coords)*scales)
    return make(high), make(low), high/(high-low)

def affine_score(d, p, gram):
    """The quotient before division by the common squared Schmidt norm."""
    def contract(k, l):
        return (d**k) @ gram @ (d**l)
    t2, t6, t10 = (p @ d**k for k in (2,6,10))
    j6 = (t6*t6-contract(6,6))/4
    j10 = (t10*t10-contract(10,10))/4
    c = (t10*t6-contract(10,6))/2
    return (t2*j10-t6*c+j6*t10), j10

def rational_witness():
    # Closed, genuinely three-dimensional Bloch pentagon on x²+y²=z².
    v = np.array([[6,0,6],[-3,4,5],[-3,-4,5],[0,8,-8],[0,-8,-8]],dtype=object)
    p = np.array([Q(k,16) for k in [6,5,5,8,8]])
    d = np.array([Q(k) for k in [1,2,3,4,5]])
    gr = lambda m: (v @ np.diag(m) @ v.T) * Q(1,512)
    mats = [gr(m) for m in ([1,1,1],[0,0,2],[2,2,0])]
    assert np.array_equal(mats[1]+mats[2],2*mats[0])
    scores = []
    for matrix in mats:
        assert np.array_equal(matrix.sum(axis=0), np.zeros(5))
        assert np.array_equal(matrix.diagonal(), p*p)
        n,b = affine_score(d,p,matrix)
        assert b > 0
        scores.append(n/b/sum(d*d))
    assert min(scores[1:]) < scores[0] < max(scores[1:])
    return scores

def check_reconstruction(rng, cases=300):
    err = 0.
    largest_gain = 0.
    strict = 0
    additional_error = 0.
    spectra_rng = np.random.default_rng(22112026)
    for k in range(cases):
        z = rng.normal(size=(5,2)) + 1j*rng.normal(size=(5,2))
        if k % 13 == 0: z[4] = 0
        if k % 17 == 0: z = z.real
        x = basis(z)
        p = (abs(x)**2).sum(axis=1)
        d = rng.uniform(.35,1.4,5)
        if k % 11 == 0: d[1]=d[3]
        d /= np.linalg.norm(d)
        y, w, theta = endpoints(x)
        grams = [bloch(frame) @ bloch(frame).T for frame in (x,y,w)]
        err = max(err, np.max(abs(grams[0]-theta*grams[1]-(1-theta)*grams[2])))
        scores = []
        for frame, gram in zip((x,y,w), grams):
            zero, direct = maximal_chain(d,frame)
            n, b = affine_score(d,p,gram)
            assert b>0
            err = max(err, abs(n/b-direct), zero, np.max(abs(frame.conj().T @ frame-np.eye(2))),
                      np.max(abs((abs(frame)**2).sum(axis=1)-p)))
            scores.append(direct)
        diff = max(scores[1:])-scores[0]
        err = max(err,-diff,scores[0]-max(scores[1:]),min(scores[1:])-scores[0])
        largest_gain=max(largest_gain,diff)
        strict+=diff>1e-10
        # The two competitors stay fixed while we change the Schmidt spectrum.
        for _ in range(3):
            other = spectra_rng.uniform(0.35, 1.4, 5)
            other /= np.linalg.norm(other)
            original, left, right = (score(other, frame) for frame in (x, y, w))
            additional_error = max(additional_error, min(left,right)-original, original-max(left,right))
    assert err < 2e-9 and additional_error < 2e-9
    print(f"{cases*3} additional spectra on the same real endpoints; largest bracketing error {additional_error:.3g}.")
    print(f"{cases} reconstructions; largest error {err:.3g}; {strict} strict gains; largest gain {largest_gain:.8f}.")

def check_spectator_family():
    """Direct Born reconstruction at representative values and an exact test just beyond the interval."""
    frame = np.zeros((5, 2))
    frame[[1, 3], 0] = np.sqrt([32/33, 1/33])
    frame[[2, 4], 1] = np.sqrt([3125/3368, 243/3368])
    raw = Q(196784800, 21446161)
    error = 0.0
    for spectator in (0.125, 0.5, 1, 1.25, 1.5, 1.875, 2):
        d = np.array([spectator, 2, 3, 4, 5])
        forbidden, success = maximal_chain(d / np.linalg.norm(d), frame)
        error = max(error, forbidden, abs(success - float(raw) / (54 + spectator**2)))
    assert error < 1e-11
    s = Q(9, 4)
    competing_pair = ((s*4**5 - 4*s**5)/(4**5+s**5))**2
    assert competing_pair + Q(1020,421)**2 > raw
    print(f"Sharp family: seven direct six-setting reconstructions, maximum discrepancy {error:.3g}.")


def search_pairing(rng):
    """Fixed spectra, real graph charts; compare the 15 pairings with local searches."""
    best_excess = 0.
    largest = 0.
    count = 0
    for run in range(16):
        d = np.exp(rng.uniform(-1,1,5)) if run else np.array([1.,2.,3.,4.,5.])
        edges = list(combinations(range(5),2))
        match = max((pair_error(d[i],d[j])**2+pair_error(d[k],d[l])**2)
                    for (i,j),(k,l) in combinations(edges,2) if len({i,j,k,l})==4) / (d@d)
        for trial in range(8):
            dd = rng.permutation(d)
            logs = np.log(dd[1:]/dd[0])
            def obj(v):
                val,grad=chart_objective(np.r_[logs,v,np.zeros(6)],5,2)
                return val, grad[4:10]
            res=minimize(obj,rng.uniform(-1,1,6),method="L-BFGS-B",jac=True,
                         bounds=[(-12,12)]*6,options={"maxiter":350,"ftol":1e-14,"gtol":1e-8})
            frame=basis(np.vstack((np.eye(2),res.x.reshape(3,2))))
            actual=score(dd/np.linalg.norm(dd),frame)
            assert abs(actual+res.fun)<1e-9
            best_excess=max(best_excess,actual-match)
            largest=max(largest,actual)
            count+=1
    print(f"{count} local trials on 16 spectra; largest positive excess over best disjoint pairing {best_excess:.3g}; highest normalized score {largest:.12f}; ceiling {P_STAR:.12f}.")

if __name__ == "__main__":
    scores=rational_witness()
    print("Exact normalized scores (original, endpoint at -1, endpoint at +1):",*[str(x) for x in scores])
    rng=np.random.default_rng(20261123)
    check_reconstruction(rng)
    check_spectator_family()
    search_pairing(rng)
