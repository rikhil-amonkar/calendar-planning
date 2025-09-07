from z3 import Int, Optimize, And, Or, Implies, Mod, sat

# Time helpers
def to_min(h, m): 
    return h * 60 + m

def to_hhmm(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

# Work hours
WORK_START = to_min(9, 0)   # 09:00
WORK_END   = to_min(17, 0)  # 17:00
MEETING_DURATION = 60       # 1 hour

# Days: 0 = Monday, 1 = Tuesday
day_names = {0: "Monday", 1: "Tuesday"}

# Busy intervals as half-open [start, end)
# Minutes from 00:00
busy = {
    0: {  # Monday
        "Gary": [
            (to_min(9,30),  to_min(10,0)),
            (to_min(11,0),  to_min(13,0)),
            (to_min(14,0),  to_min(14,30)),
            (to_min(16,30), to_min(17,0)),
        ],
        "David": [
            (to_min(9,0),   to_min(9,30)),
            (to_min(10,0),  to_min(13,0)),
            (to_min(14,30), to_min(16,30)),
        ],
    },
    1: {  # Tuesday
        "Gary": [
            (to_min(9,0),   to_min(9,30)),
            (to_min(10,30), to_min(11,0)),
            (to_min(14,30), to_min(16,0)),
        ],
        "David": [
            (to_min(9,0),   to_min(9,30)),
            (to_min(10,0),  to_min(10,30)),
            (to_min(11,0),  to_min(12,30)),
            (to_min(13,0),  to_min(14,30)),
            (to_min(15,0),  to_min(16,0)),
            (to_min(16,30), to_min(17,0)),
        ],
    },
}

# Z3 variables
day = Int('day')      # 0 = Monday, 1 = Tuesday
start = Int('start')  # meeting start in minutes since midnight
end = Int('end')      # meeting end in minutes since midnight

opt = Optimize()

# Domain constraints
opt.add(And(day >= 0, day <= 1))
opt.add(end == start + MEETING_DURATION)
opt.add(And(start >= WORK_START, end <= WORK_END))

# Nice calendar alignment (30-minute increments)
opt.add(Mod(start, 30) == 0)

# No overlap constraints for each participant and each day's busy intervals
for d in [0, 1]:
    for person in ["Gary", "David"]:
        for (b_start, b_end) in busy[d][person]:
            # Meeting does not overlap busy block: end <= b_start OR start >= b_end
            opt.add(Implies(day == d, Or(end <= b_start, start >= b_end)))

# Optional: prefer earliest day, then earliest time
opt.minimize(day)
opt.minimize(start)

if opt.check() == sat:
    model = opt.model()
    d_val = model[day].as_long()
    s_val = model[start].as_long()
    e_val = model[end].as_long()
    day_str = day_names[d_val]
    s_str = to_hhmm(s_val)
    e_str = to_hhmm(e_val)
    print(f"{day_str} {{{s_str}:{e_str}}}")
else:
    print("No feasible meeting time found.")