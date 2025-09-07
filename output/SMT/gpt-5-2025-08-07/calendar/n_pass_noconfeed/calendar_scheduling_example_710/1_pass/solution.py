from z3 import *

# Meeting parameters
duration = 30  # minutes
work_start = 9 * 60   # 09:00 in minutes
work_end   = 17 * 60  # 17:00 in minutes

# Days: 0=Monday, 1=Tuesday, 2=Wednesday
days = ["Monday", "Tuesday", "Wednesday"]

# Z3 variables
day = Int('day')
start = Int('start')  # start time in minutes from 00:00 on that day

s = Solver()

# Domain constraints
s.add(And(day >= 0, day <= 2))
s.add(day != 2)  # Cheryl cannot meet on Wednesday
s.add(start >= work_start, start + duration <= work_end)
s.add(start % 30 == 0)  # align to 30-minute boundary

# Busy schedules (intervals are [start, end) in minutes from 00:00)
# Cheryl
cheryl_busy = {
    0: [(9*60, 9*60+30), (11*60+30, 13*60), (15*60+30, 16*60)],
    1: [(15*60, 15*60+30)],
    2: []  # Not needed; she can't meet on Wednesday
}

# Kyle
kyle_busy = {
    0: [(9*60, 17*60)],
    1: [(9*60+30, 17*60)],
    2: [(9*60, 9*60+30), (10*60, 13*60), (13*60+30, 14*60), (14*60+30, 17*60)]
}

def no_overlap_for_day(day_var, intervals):
    for d, ivals in intervals.items():
        for (bs, be) in ivals:
            # If it's that day, the meeting [start, start+duration) must not overlap [bs, be)
            s.add(Implies(day_var == d, Or(start + duration <= bs, start >= be)))

# Apply non-overlap constraints for both participants
no_overlap_for_day(day, cheryl_busy)
no_overlap_for_day(day, kyle_busy)

# Solve
if s.check() == sat:
    m = s.model()
    day_idx = m[day].as_long()
    start_min = m[start].as_long()
    end_min = start_min + duration

    def fmt(t):
        h = t // 60
        mi = t % 60
        return f"{h:02d}:{mi:02d}"

    time_range = f"{{{fmt(start_min)}:{fmt(end_min)}}}"
    print(f"{days[day_idx]} {time_range}")
else:
    print("No feasible meeting time found.")