from z3 import Solver, Int, Or, And, sat

# Helper functions
def to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Problem setup
day = "Monday"
work_start = to_min("09:00")
work_end   = to_min("17:00")
duration = 30  # minutes

# Busy intervals per participant (inclusive of start, exclusive of end)
busy = {
    "Andrea": [],
    "Jack": [
        ("09:00", "09:30"),
        ("14:00", "14:30"),
    ],
    "Madison": [
        ("09:30", "10:30"),
        ("13:00", "14:00"),
        ("15:00", "15:30"),
        ("16:30", "17:00"),
    ],
    "Rachel": [
        ("09:30", "10:30"),
        ("11:00", "11:30"),
        ("12:00", "13:30"),
        ("14:30", "15:30"),
        ("16:00", "17:00"),
    ],
    "Douglas": [
        ("09:00", "11:30"),
        ("12:00", "16:30"),
    ],
    "Ryan": [
        ("09:00", "09:30"),
        ("13:00", "14:00"),
        ("14:30", "17:00"),
    ],
}

# Convert all busy intervals to minutes
busy_min = []
for person, intervals in busy.items():
    for s, e in intervals:
        busy_min.append((to_min(s), to_min(e)))

# Z3 model
s = Solver()
start = Int("start")
# Meeting within work hours
s.add(start >= work_start)
s.add(start + duration <= work_end)

# No overlap with any busy interval
for (b_s, b_e) in busy_min:
    s.add(Or(start + duration <= b_s, start >= b_e))

# Solve
if s.check() == sat:
    m = s.model()
    start_val = m[start].as_long()
    end_val = start_val + duration
    print(f"{day} {{{fmt(start_val)}:{fmt(end_val)}}}")
else:
    print("No feasible time found.")