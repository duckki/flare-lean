# Same original finite binary64 inputs and four separately rounded stages as
# Kalman.Implementation.TinyEKFClock.nextMean. No FMA; any assistance is listed below.
@rnd = float<ieee_64, ne>;
x = rnd(xx);
z = rnd(zz);
k = rnd(kk);
r = rnd(z - x);
m = rnd(r * k);
a = rnd(m + 0);
y = rnd(a + x);
f = x + k * (z - x);

{ x in [-1,1] /\ z in [-0.5,0.5] /\ k in [0,1] ->
  r in [-4,4] /\ m in [-4,4] /\ a in [-4,4] /\ y in [-2,2] /\
  y - f in [-1b-51,1b-51] }

# Assisted attempt: expose the rounding-error telescope and convex reference.
y - f -> (y - (a + x)) + (a - (m + 0)) + (m - r * k) + k * (r - (z - x));
y -> (1 - k) * x + k * z + (y - f);
