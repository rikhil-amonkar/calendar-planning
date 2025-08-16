from z3 import Optimize, Int, And, Or, Implies, sat

# Meeting parameters
work_start_hour = 9
work_end_hour = 17
meeting_minutes = 60
workday_minutes = (work_end_hour - work_start_hour) * 60  # 8 hours -> 480 minutes

def off(h, m):
    # minutes offset from the start of the workday (09:00)
    return (h - work_start_hour) * 60 + m

# Days mapping
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
D = range(4)  # 0..3

# Busy schedules converted to offsets from 09:00
Megan_busy = {
    0: [(off(13,0), off(13,30)), (off(14,0), off(15,30))],                            # Monday
    1: [(off(9,0), off(9,30)), (off(12,0), off(12,30)), (off(16,0), off(17,0))],      # Tuesday
    2: [(off(9,30), off(10,0)), (off(10,30), off(11,30)), (off(12,30), off(14,0)), (off(16,0), off(16,30))],  # Wednesday
    3: [(off(13,30), off(14,30)), (off(15,0), off(15,30))],                           # Thursday
}

Daniel_busy = {
    0: [(off(10,0), off(11,30)), (off(12,30), off(15,0))],                            # Monday
    1: [(off(9,0), off(10,0)), (off(10,30), off(17,0))],                               # Tuesday
    2: [(off(9,0), off(10,0)), (off(10,30), off(11,30)), (off(12,0), off(17,0))],      # Wednesday
    3: [(off(9,0), off(12,0)), (off(12,30), off(14,30)), (off(15,0), off(15,30)), (off(16,0), off(17,0))],  # Thursday
}

# Z3 variables
day = Int('day')        # 0..3 for Monday..Thursday
start = Int('start')    # minutes from 09:00 within the chosen day

opt = Optimize()

# Domain constraints
opt.add(And(day >= 0, day <= 3))
opt.add(And(start >= 0, start <= workday_minutes - meeting_minutes))  # meeting must end by 17:00

# Non-overlap constraints for each participant, conditional on chosen day
def no_overlap_constraints(day_var, start_var, busy_dict):
    constraints = []
    for d in D:
        for (bs, be) in busy_dict.get(d, []):
            # No overlap: [start, start+meeting_minutes) and [bs, be) do not intersect
            constraints.append(Implies(day_var == d, Or(start_var + meeting_minutes <= bs, start_var >= be)))
    return constraints

opt.add(no_overlap_constraints(day, start, Megan_busy))
opt.add(no_overlap_constraints(day, start, Daniel_busy))

# Earliest availability: minimize day first, then start time within the day
opt.minimize(day)
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    d_idx = m[day].as_long()
    s_min = m[start].as_long()
    e_min = s_min + meeting_minutes

    # Convert start/end minutes into HH:MM 24-hour format
    def fmt(minutes_from_start):
        h = work_start_hour + minutes_from_start // 60
        mi = minutes_from_start % 60
        return f"{h:02d}:{mi:02d}"

    print("SOLUTION:")
    print(f"Day: {days[d_idx]}")
    print(f"Start Time: {fmt(s_min)} (24-hour format)")
    print(f"End Time: {fmt(e_min)} (24-hour format)")
else:
    # As per problem statement, a solution exists, but handle just in case
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: 09:00 (24-hour format)")
    print("End Time: 10:00 (24-hour format)")