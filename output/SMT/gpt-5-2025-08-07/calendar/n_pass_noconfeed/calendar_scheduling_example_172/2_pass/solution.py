from z3 import *

# Meeting parameters
DURATION = 30  # minutes (0.5 hours)
WORK_START = 9 * 60
WORK_END = 17 * 60
DAY = "Monday"

# Busy intervals for each participant as (start_min, end_min) in minutes since 00:00
def minutes(h, m):
    return h * 60 + m

patrick_busy = [
    (minutes(9, 0),  minutes(9, 30)),
    (minutes(10, 0), minutes(10, 30)),
    (minutes(13, 30), minutes(14, 0)),
    (minutes(16, 0), minutes(16, 30)),
]

kayla_busy = [
    (minutes(12, 30), minutes(13, 30)),
    (minutes(15, 0), minutes(15, 30)),
    (minutes(16, 0), minutes(16, 30)),
]

carl_busy = [
    (minutes(10, 30), minutes(11, 0)),
    (minutes(12, 0),  minutes(12, 30)),
    (minutes(13, 0),  minutes(13, 30)),
    (minutes(14, 30), minutes(17, 0)),
]

christian_busy = [
    (minutes(9, 0),  minutes(12, 30)),
    (minutes(13, 0), minutes(14, 0)),
    (minutes(14, 30), minutes(17, 0)),
]

participants_busy = [patrick_busy, kayla_busy, carl_busy, christian_busy]

# Solver
opt = Optimize()
start = Int('start')
end = Int('end')

# Working hours and duration constraints
opt.add(start >= WORK_START)
opt.add(end <= WORK_END)
opt.add(end - start == DURATION)

# Align meeting to 30-minute increments
opt.add(start % 30 == 0)
opt.add(end % 30 == 0)

# No-overlap constraints for each participant
for busy_list in participants_busy:
    for (b_start, b_end) in busy_list:
        # Meeting [start, end) does not overlap [b_start, b_end)
        opt.add(Or(end <= b_start, start >= b_end))

# Prefer the earliest feasible time
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    s = m[start].as_long()
    e = m[end].as_long()

    def fmt(mm):
        hh = mm // 60
        mi = mm % 60
        return f"{hh:02d}:{mi:02d}"

    start_str = fmt(s)
    end_str = fmt(e)

    # Output as a single plan object
    plan = {'day': DAY, 'time_range': f"{{{start_str}:{end_str}}}"}
    print(plan)
else:
    print("No feasible time found.")