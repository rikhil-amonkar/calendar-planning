from z3 import *

# Helper to convert HH:MM to minutes since midnight
def mm(h, m):
    return h * 60 + m

# Pretty-print minutes to HH:MM
def to_hhmm(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Workday and meeting settings
DAY = "Monday"
WORK_START = mm(9, 0)    # 09:00
WORK_END   = mm(17, 0)   # 17:00
DURATION   = 30          # minutes

# Participants' busy intervals for Monday (half-open intervals [start, end))
busy = {
    "Steven": [],
    "Roy": [],
    "Cynthia": [
        (mm(9,30),  mm(10,30)),
        (mm(11,30), mm(12, 0)),
        (mm(13, 0), mm(13,30)),
        (mm(15, 0), mm(16, 0)),
    ],
    "Lauren": [
        (mm(9, 0),  mm(9, 30)),
        (mm(10,30), mm(11, 0)),
        (mm(11,30), mm(12, 0)),
        (mm(13, 0), mm(13,30)),
        (mm(14, 0), mm(14,30)),
        (mm(15, 0), mm(15,30)),
        (mm(16, 0), mm(17, 0)),
    ],
    "Robert": [
        (mm(10,30), mm(11, 0)),
        (mm(11,30), mm(12, 0)),
        (mm(12,30), mm(13,30)),
        (mm(14, 0), mm(16, 0)),
    ],
}

# Z3 model
opt = Optimize()
S = Int("start")  # meeting start time in minutes
E = Int("end")    # meeting end time in minutes

# Duration and bounds
opt.add(E == S + DURATION)
opt.add(S >= WORK_START, E <= WORK_END)

# Align to 30-minute grid (optional but typical for half-hour meetings)
opt.add(S % 30 == 0)

# No overlap with each participant's busy intervals
for person, intervals in busy.items():
    for (bs, be) in intervals:
        # Meeting must be entirely before the busy slot or start after it ends
        opt.add(Or(E <= bs, S >= be))

# Earliest availability
opt.minimize(S)

if opt.check() == sat:
    m = opt.model()
    start = m[S].as_long()
    end = m[E].as_long()
    start_str = to_hhmm(start)
    end_str = to_hhmm(end)
    # Output must include both the day and the time range in {HH:MM:HH:MM}
    print(DAY)
    print(f"{{{start_str}:{end_str}}}")
else:
    print("No feasible meeting time found.")