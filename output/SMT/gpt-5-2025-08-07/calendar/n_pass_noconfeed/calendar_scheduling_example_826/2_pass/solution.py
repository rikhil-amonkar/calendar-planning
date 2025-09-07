from z3 import Int, Optimize, And, Or, If, sat

# Meeting parameters
DURATION = 30  # minutes
WORK_START = 9 * 60  # 09:00 in minutes
WORK_END = 17 * 60   # 17:00 in minutes
REL_START = 0
REL_END = WORK_END - WORK_START  # 480 minutes

# Days mapping
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

# Helper to convert HH:MM to minutes from 09:00
def to_rel(h, m):
    return (h * 60 + m) - WORK_START

# James's busy calendar (relative to 09:00)
james_busy = {
    0: [  # Monday
        (to_rel(9, 0), to_rel(9, 30)),
        (to_rel(10, 30), to_rel(11, 0)),
        (to_rel(12, 30), to_rel(13, 0)),
        (to_rel(14, 30), to_rel(15, 30)),
        (to_rel(16, 30), to_rel(17, 0)),
    ],
    1: [  # Tuesday
        (to_rel(9, 0), to_rel(11, 0)),
        (to_rel(11, 30), to_rel(12, 0)),
        (to_rel(12, 30), to_rel(15, 30)),
        (to_rel(16, 0), to_rel(17, 0)),
    ],
    2: [  # Wednesday
        (to_rel(10, 0), to_rel(11, 0)),
        (to_rel(12, 0), to_rel(13, 0)),
        (to_rel(13, 30), to_rel(16, 0)),
    ],
    3: [  # Thursday
        (to_rel(9, 30), to_rel(11, 30)),
        (to_rel(12, 0), to_rel(12, 30)),
        (to_rel(13, 0), to_rel(13, 30)),
        (to_rel(14, 0), to_rel(14, 30)),
        (to_rel(16, 30), to_rel(17, 0)),
    ],
}

# Cheryl is wide open; no busy intervals needed.

# Z3 variables
day = Int("day")      # 0=Mon,1=Tue,2=Wed,3=Thu
start = Int("start")  # minutes relative to 09:00

opt = Optimize()
opt.set(priority='lex')  # ensure earliest day, then earliest time

# Domain constraints
opt.add(And(day >= 0, day <= 3))
opt.add(And(start >= REL_START, start + DURATION <= REL_END))
opt.add(start % 30 == 0)  # half-hour granularity

# Non-overlap constraints for James on the chosen day
for d in range(4):
    no_overlaps = []
    for (b, e) in james_busy[d]:
        # Meeting [start, start+DURATION) must be entirely outside [b, e)
        no_overlaps.append(Or(start + DURATION <= b, start >= e))
    if no_overlaps:
        opt.add(If(day == d, And(*no_overlaps), True))

# Preference: earliest day, then earliest time
opt.minimize(day)
opt.minimize(start)

if opt.check() != sat:
    raise RuntimeError("No feasible meeting could be scheduled.")

m = opt.model()
d_val = m[day].as_long()
s_val = m[start].as_long()

# Convert to absolute times
abs_start = WORK_START + s_val
abs_end = abs_start + DURATION

def fmt(minutes):
    h = minutes // 60
    mm = minutes % 60
    return f"{h:02d}:{mm:02d}"

day_name = days[d_val]
start_str = fmt(abs_start)
end_str = fmt(abs_end)

# Output: day of week, and time range in {HH:MM:HH:MM}
print(day_name)
print(f"{{{start_str}:{end_str}}}")