from z3 import Optimize, Int, And, Or, Implies, sat

def to_minutes(h, m):
    return h * 60 + m

def fmt_time(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Problem setup
days = ["Monday", "Tuesday", "Wednesday"]
work_start = to_minutes(9, 0)
work_end   = to_minutes(17, 0)
duration   = 60  # minutes

# Busy schedules (minutes from midnight)
# Roy's busy times
busy = {
    0: [  # Monday
        (to_minutes(10, 0),  to_minutes(11, 30)),
        (to_minutes(12, 0),  to_minutes(13, 0)),
        (to_minutes(14, 0),  to_minutes(14, 30)),
        (to_minutes(15, 0),  to_minutes(17, 0)),
    ],
    1: [  # Tuesday
        (to_minutes(10, 30), to_minutes(11, 30)),
        (to_minutes(12, 0),  to_minutes(14, 30)),
        (to_minutes(15, 0),  to_minutes(15, 30)),
        (to_minutes(16, 0),  to_minutes(17, 0)),
    ],
    2: [  # Wednesday
        (to_minutes(9, 30),  to_minutes(11, 30)),
        (to_minutes(12, 30), to_minutes(14, 0)),
        (to_minutes(14, 30), to_minutes(15, 30)),
        (to_minutes(16, 30), to_minutes(17, 0)),
    ],
}

# Z3 variables
D = Int('D')      # day index: 0=Mon, 1=Tue, 2=Wed
S = Int('S')      # start time in minutes after 09:00 (within work day)

opt = Optimize()
opt.set(priority='lex')

# Domain constraints
opt.add(D >= 0, D <= 2)
# Meeting entirely within work hours [09:00, 17:00)
opt.add(S >= 0)
opt.add(S + duration <= (work_end - work_start))
# Optional: schedule on 30-minute grid
opt.add(S % 30 == 0)

# Non-overlap constraints for Roy (Patrick has no busy constraints)
for d in range(3):
    constraints = []
    for (bs, be) in busy[d]:
        # Convert to offsets from 09:00
        bs_off = bs - work_start
        be_off = be - work_start
        # No overlap: (S + dur <= bs) or (S >= be)
        constraints.append(Or(S + duration <= bs_off, S >= be_off))
    # Apply only on the chosen day
    if constraints:
        opt.add(Implies(D == d, And(constraints)))
    else:
        opt.add(Implies(D == d, True))

# Objective: earliest availability (lex: first day, then time)
opt.minimize(D)
opt.minimize(S)

if opt.check() == sat:
    m = opt.model()
    d_idx = m[D].as_long()
    start_off = m[S].as_long()
    start_abs = work_start + start_off
    end_abs   = start_abs + duration
    day_name = days[d_idx]
    start_str = fmt_time(start_abs)
    end_str   = fmt_time(end_abs)
    # Output includes both day and time range {HH:MM:HH:MM}
    print(f"{day_name} {{{start_str}:{end_str}}}")
else:
    print("No solution found.")