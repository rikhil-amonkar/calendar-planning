# Meeting Scheduler using Z3 SMT Solver
# Finds a 30-minute meeting slot for Walter, Cynthia, Ann, Catherine, and Kyle on Monday between 09:00 and 17:00.

try:
    from z3 import Int, Or, Optimize, sat
except ImportError:
    import sys
    import subprocess
    subprocess.check_call([sys.executable, "-m", "pip", "install", "z3-solver"])
    from z3 import Int, Or, Optimize, sat

def t(h, m):
    return h * 60 + m

def fmt(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Work window
DAY = "Monday"
DAY_START = t(9, 0)
DAY_END = t(17, 0)
DURATION = 30  # minutes

# Participants' busy intervals (half-open [start, end))
walter = []
cynthia = [
    (t(9, 0), t(9, 30)),
    (t(10, 0), t(10, 30)),
    (t(13, 30), t(14, 30)),
    (t(15, 0), t(16, 0)),
]
ann = [
    (t(10, 0), t(11, 0)),
    (t(13, 0), t(13, 30)),
    (t(14, 0), t(15, 0)),
    (t(16, 0), t(16, 30)),
]
catherine = [
    (t(9, 0), t(11, 30)),
    (t(12, 30), t(13, 30)),
    (t(14, 30), t(17, 0)),
]
kyle = [
    (t(9, 0), t(9, 30)),
    (t(10, 0), t(11, 30)),
    (t(12, 0), t(12, 30)),
    (t(13, 0), t(14, 30)),
    (t(15, 0), t(16, 0)),
]

# Combine all busy intervals (each must be avoided)
all_busy = walter + cynthia + ann + catherine + kyle

opt = Optimize()
start = Int("start")

# Basic time window constraints
opt.add(start >= DAY_START)
opt.add(start + DURATION <= DAY_END)

# Avoid overlaps with all busy intervals: meeting end <= busy start OR meeting start >= busy end
for (bs, be) in all_busy:
    opt.add(Or(start + DURATION <= bs, start >= be))

# Optional: pick the earliest feasible start for determinism
opt.minimize(start)

if opt.check() != sat:
    raise RuntimeError("No feasible meeting time found, but the problem statement guarantees one exists.")

model = opt.model()
s_val = model[start].as_long()
e_val = s_val + DURATION

print(DAY)
print(f"{{{fmt(s_val)}:{fmt(e_val)}}}")