import numpy as np
def bloch(psi):
    a,b = psi/np.linalg.norm(psi)
    return np.array([2*(np.conj(a)*b).real, 2*(np.conj(a)*b).imag, abs(a)**2-abs(b)**2])
# Gudder / our bi-normalized binary law: a+b=1, |a|^2+|b|^2=1
th = np.linspace(0, np.pi, 9)
print("Gudder curve a=cos t e^{it}, b=-i sin t e^{it}: check constraints + Bloch image")
for t in th:
    a = np.cos(t)*np.exp(1j*t); b = -1j*np.sin(t)*np.exp(1j*t)
    print(f" t={t/np.pi:5.3f}pi  a+b={a+b:.3f}  |a|^2+|b|^2={abs(a)**2+abs(b)**2:.3f}  bloch={np.round(bloch(np.array([a,b])),3)}")
# general solution set: |a-1/2|=1/2 circle; is the Bloch image always the x=0 great circle?
r = np.random.default_rng(0)
xs = []
for _ in range(1000):
    phi = r.uniform(0,2*np.pi); a = 0.5+0.5*np.exp(1j*phi); b = 1-a
    xs.append(bloch(np.array([a,b]))[0])
print("max |bloch_x| over ALL solutions of the two sums:", np.max(np.abs(xs)))
# balanced root t=pi/4 and the octant Berry phase
s0 = np.array([1,0]); sp = np.array([1,1])/np.sqrt(2); smi = np.array([1,-1j])/np.sqrt(2)
B = np.vdot(s0,sp)*np.vdot(sp,smi)*np.vdot(smi,s0)
print("Bloch vectors |0>,|+>,|-i>:", bloch(s0), bloch(sp), bloch(smi))
print("Bargmann invariant phase arg<0|+><+|-i><-i|0> =", np.angle(B)/np.pi, "pi")
print("octant solid angle 4pi/8 =", 0.5, "pi ; half of it =", 0.25, "pi")
a = np.cos(np.pi/4)*np.exp(1j*np.pi/4)
print("root amplitude a(pi/4) =", np.round(a,4), " arg =", np.angle(a)/np.pi, "pi")
# k children: balanced root needs sum of k unit phasors = sqrt(k)
for k in [2,3,4]:
    # symmetric family check: minimal max-phase solution exists?
    print(f" k={k}: balanced root needs |sum of {k} unit phasors| = sqrt({k}) = {np.sqrt(k):.4f}")
al = np.arccos((np.sqrt(3)-1)/2); print(" k=3 symmetric root phases (a,0,-a), a =", al/np.pi, "pi =", np.degrees(al), "deg")
