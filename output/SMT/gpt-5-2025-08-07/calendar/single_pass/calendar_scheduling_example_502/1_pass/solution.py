from z3 import Optimize, Int, Or, If, sat

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Workday bounds
work_start = minutes(9, 0)
work_end = minutes(17, 0)
duration = 30

# Busy intervals (start, end) in minutes since midnight
jack_busy = [
    (minutes(9, 30), minutes(10, 30)),
    (minutes(11, 0), minutes(11, 30)),
    (minutes(12, 30), minutes(13, 0)),
    (minutes(14, 0), minutes(14, 30)),
    (minutes(16, 0), minutes(16, 30)),
]

charlotte_busy = [
    (minutes(9, 30), minutes(10, 0)),
    (minutes(10, 30), minutes(12, 0)),
    (minutes(12, 30), minutes(13, 30)),
    (minutes(14, 0), minutes(16, 0)),
]

# Preference: Jack would like to avoid meetings after 12:30
avoid_after = minutes(12, 30)

opt = Optimize()

start = Int('start')
end = Int('end')

# Core constraints
opt.add(start >= work_start)
opt.add(end == start + duration)
opt.add(end <= work_end)

# Non-overlap constraints
def no_overlap_constraints(busy_intervals):
    cons = []
    for s, e in busy_intervals:
        cons.append(Or(end <= s, start >= e))
    return cons

opt.add(no_overlap_constraints(jack_busy))
opt.add(no_overlap_constraints(charlotte_busy))

# Soft preference: prefer meeting before 12:30 (start time before 12:30)
penalty_after_pref = Int('penalty_after_pref')
opt.add(penalty_after_pref == If(start >= avoid_after, 1, 0))

# Optimize: first minimize violating the preference, then pick earliest start
opt.minimize(penalty_after_pref)
opt.minimize(start)

if opt.check() != sat:
    raise RuntimeError("No feasible schedule found, but a solution was expected.")

model = opt.model()
start_min = model[start].as_long()
end_min = model[end].as_long()

print("SOLUTION:")
print("Day: Monday")
print(f"Start Time: {fmt_time(start_min)} (24-hour format)")
print(f"End Time: {fmt_time(end_min)} (24-hour format)")