from z3 import *

# Helper functions
def hm_to_min(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def min_to_hm(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Meeting parameters
WORK_START = hm_to_min("09:00")
WORK_END   = hm_to_min("17:00")
DURATION   = 60  # minutes
DAYS = ["Monday", "Tuesday"]

# Participants' busy schedules per day
# Intervals are half-open [start, end)
patricia = {
    0: [("10:00","10:30"), ("11:30","12:00"), ("13:00","13:30"), ("14:30","15:30"), ("16:00","16:30")],  # Monday
    1: [("10:00","10:30"), ("11:00","12:00"), ("14:00","16:00"), ("16:30","17:00")]                      # Tuesday
}
jesse = {
    0: [("09:00","17:00")],  # Monday
    1: [("11:00","11:30"), ("12:00","12:30"), ("13:00","14:00"), ("14:30","15:00"), ("15:30","17:00")]  # Tuesday
}

# Convert schedules to minutes
def convert_schedule(sched):
    out = {}
    for d, intervals in sched.items():
        out[d] = [(hm_to_min(s), hm_to_min(e)) for s, e in intervals]
    return out

patricia_m = convert_schedule(patricia)
jesse_m = convert_schedule(jesse)

# Z3 Variables
day = Int("day")           # 0 = Monday, 1 = Tuesday
start = Int("start")       # minutes from 00:00
end = Int("end")

s = Solver()

# Domain constraints
s.add(Or(day == 0, day == 1))
s.add(start >= WORK_START)
s.add(end == start + DURATION)
s.add(end <= WORK_END)

# Non-overlap constraints for each participant on the chosen day
def no_overlap_with(schedule):
    for d in [0,1]:
        for (b_start, b_end) in schedule[d]:
            # Meeting [start,end) does not overlap busy [b_start,b_end)
            s.add(Implies(day == d, Or(end <= b_start, start >= b_end)))

no_overlap_with(patricia_m)
no_overlap_with(jesse_m)

# Solve
if s.check() == sat:
    m = s.model()
    chosen_day = DAYS[m[day].as_long()]
    st = m[start].as_long()
    en = m[end].as_long()
    print(f"{chosen_day} {{{min_to_hm(st)}:{min_to_hm(en)}}}")
else:
    print("No solution found")