from z3 import *

# Meeting parameters
DURATION = 30  # minutes
WORK_START = 9 * 60   # 09:00 in minutes
WORK_END = 17 * 60    # 17:00 in minutes

# Days: 0=Monday, 1=Tuesday, 2=Wednesday
day_names = ["Monday", "Tuesday", "Wednesday"]

# Samuel's busy intervals per day (in minutes from 00:00 of that day)
busy = {
    0: [  # Monday
        (10*60 + 30, 11*60 + 0),   # 10:30-11:00
        (12*60 + 0,  12*60 + 30),  # 12:00-12:30
        (13*60 + 0,  15*60 + 0),   # 13:00-15:00
        (15*60 + 30, 16*60 + 30),  # 15:30-16:30
    ],
    1: [  # Tuesday
        (9*60 + 0,   12*60 + 0),   # 09:00-12:00
        (14*60 + 0,  15*60 + 30),  # 14:00-15:30
        (16*60 + 30, 17*60 + 0),   # 16:30-17:00
    ],
    2: [  # Wednesday
        (10*60 + 30, 11*60 + 0),   # 10:30-11:00
        (11*60 + 30, 12*60 + 0),   # 11:30-12:00
        (12*60 + 30, 13*60 + 0),   # 12:30-13:00
        (14*60 + 0,  14*60 + 30),  # 14:00-14:30
        (15*60 + 0,  16*60 + 0),   # 15:00-16:00
    ]
}
# Larry is free all week; no busy intervals needed for Larry.

# Z3 variables
day = Int('day')      # 0..2 (Mon..Wed)
start = Int('start')  # minutes from 00:00 of selected day
penalty = Int('penalty')

opt = Optimize()
opt.set(priority='lex')

# Domain constraints
opt.add(And(day >= 0, day <= 2))
opt.add(And(start >= WORK_START, start + DURATION <= WORK_END))

# No-overlap constraints for Samuel based on selected day
for d in [0, 1, 2]:
    constraints = []
    for (s, e) in busy[d]:
        # Meeting [start, start + DURATION) must not intersect [s, e)
        constraints.append(Or(start + DURATION <= s, start >= e))
    if constraints:
        opt.add(Implies(day == d, And(constraints)))
    else:
        opt.add(Implies(day == d, True))

# Preferences (soft constraints as penalties):
# - Larry would rather not meet on Wednesday (day == 2)
# - Samuel would like to avoid more meetings on Tuesday (day == 1)
opt.add(penalty == If(day == 2, 1, 0) + If(day == 1, 1, 0))

# Objectives:
# 1) Minimize penalty (respect preferences)
# 2) Earliest day
# 3) Earliest start time
opt.minimize(penalty)
opt.minimize(day)
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    d = m[day].as_long()
    s = m[start].as_long()
    e = s + DURATION

    def fmt(t):
        hh = t // 60
        mm = t % 60
        return f"{hh:02d}:{mm:02d}"

    day_str = day_names[d]
    start_str = fmt(s)
    end_str = fmt(e)

    # Output format: Day and time range {HH:MM:HH:MM}
    print(f"{day_str} {{{start_str}:{end_str}}}")
else:
    print("No solution found.")