from z3 import *

def minutes(h, m):
    return h * 60 + m

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Meeting parameters
duration = 30  # minutes
work_start = minutes(9, 0)
work_end = minutes(17, 0)

# Participants' busy schedules on Monday (start, end) in minutes since midnight
juan_busy = [
    (minutes(9, 0), minutes(10, 30)),
    (minutes(15, 30), minutes(16, 0)),
]
marilyn_busy = [
    (minutes(11, 0), minutes(11, 30)),
    (minutes(12, 30), minutes(13, 0)),
]
ronald_busy = [
    (minutes(9, 0), minutes(10, 30)),
    (minutes(12, 0), minutes(12, 30)),
    (minutes(13, 0), minutes(13, 30)),
    (minutes(14, 0), minutes(16, 30)),
]

# Juan cannot meet after 16:00, so meeting must end by 16:00
juan_latest_end = minutes(16, 0)

# Z3 variables
start = Int('start')
end = Int('end')

opt = Optimize()

# Basic constraints
opt.add(end == start + duration)
opt.add(start >= work_start)
opt.add(end <= work_end)
opt.add(end <= juan_latest_end)  # honoring Juan's "not after 16:00" constraint

# Optional: align to 30-minute boundaries
opt.add(start % 30 == 0)

# Helper: meeting [start, end) does not overlap with busy [b_start, b_end)
def no_overlap(b_start, b_end):
    return Or(end <= b_start, start >= b_end)

# Add non-overlap constraints for all participants
for (bs, be) in juan_busy:
    opt.add(no_overlap(bs, be))
for (bs, be) in marilyn_busy:
    opt.add(no_overlap(bs, be))
for (bs, be) in ronald_busy:
    opt.add(no_overlap(bs, be))

# Prefer earliest feasible time
opt.minimize(start)

if opt.check() == sat:
    model = opt.model()
    s_val = model[start].as_long()
    e_val = model[end].as_long()
    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {minutes_to_str(s_val)}")
    print(f"End Time: {minutes_to_str(e_val)}")
else:
    # Problem statement guarantees a solution exists; this is a fallback.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: 00:00")
    print("End Time: 00:30")