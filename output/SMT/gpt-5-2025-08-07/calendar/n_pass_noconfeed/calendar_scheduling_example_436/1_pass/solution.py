# Meeting scheduler using Z3 SMT solver
# Finds a 30-minute meeting time on Monday between 09:00 and 17:00
# that does not conflict with any participant's existing meetings.

from z3 import Optimize, Int, Or, And, sat

def m(h, mi):
    return h * 60 + mi

def fmt(t):
    return f"{t//60:02d}:{t%60:02d}"

# Workday constraints (Monday)
WORK_START = m(9, 0)
WORK_END = m(17, 0)
DURATION = 30

# Participants' busy schedules on Monday (start, end) in minutes since midnight
busy_intervals = []
# Patrick: 13:30-14:00, 14:30-15:00
busy_intervals += [(m(13,30), m(14,0)), (m(14,30), m(15,0))]
# Shirley: 9:00-9:30, 11:00-11:30, 12:00-12:30, 14:30-15:00, 16:00-17:00
busy_intervals += [(m(9,0), m(9,30)), (m(11,0), m(11,30)), (m(12,0), m(12,30)), (m(14,30), m(15,0)), (m(16,0), m(17,0))]
# Jeffrey: 9:00-9:30, 10:30-11:00, 11:30-12:00, 13:00-13:30, 16:00-17:00
busy_intervals += [(m(9,0), m(9,30)), (m(10,30), m(11,0)), (m(11,30), m(12,0)), (m(13,0), m(13,30)), (m(16,0), m(17,0))]
# Gloria: 11:30-12:00, 15:00-15:30
busy_intervals += [(m(11,30), m(12,0)), (m(15,0), m(15,30))]
# Nathan: 9:00-9:30, 10:30-12:00, 14:00-17:00
busy_intervals += [(m(9,0), m(9,30)), (m(10,30), m(12,0)), (m(14,0), m(17,0))]
# Angela: 9:00-9:30, 10:00-11:00, 12:30-15:00, 15:30-16:30
busy_intervals += [(m(9,0), m(9,30)), (m(10,0), m(11,0)), (m(12,30), m(15,0)), (m(15,30), m(16,30))]
# David: 9:00-9:30, 10:00-10:30, 11:00-14:00, 14:30-16:30
busy_intervals += [(m(9,0), m(9,30)), (m(10,0), m(10,30)), (m(11,0), m(14,0)), (m(14,30), m(16,30))]

# Z3 model
opt = Optimize()
start = Int('start')

# Within work hours
opt.add(And(start >= WORK_START, start + DURATION <= WORK_END))

# No overlap with any busy interval
for bs, be in busy_intervals:
    opt.add(Or(start + DURATION <= bs, start >= be))

# Prefer the earliest feasible time
opt.minimize(start)

if opt.check() == sat:
    model = opt.model()
    s = model[start].as_long()
    e = s + DURATION
    # Output must include both the time range and the day of the week
    print(f"Monday {{{fmt(s)}:{fmt(e)}}}")
else:
    print("No feasible time found.")