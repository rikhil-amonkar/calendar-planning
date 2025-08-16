from z3 import Optimize, Int, And, Or, Implies

# Time helpers
def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt_hhmm(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

# Constants
WORK_START = to_minutes("09:00")
WORK_END = to_minutes("17:00")
DURATION = 30  # minutes
DAY_NAMES = ["Monday", "Tuesday", "Wednesday"]

# Convert absolute times to offsets from WORK_START for constraints
def offset(hhmm):
    return to_minutes(hhmm) - WORK_START

# Busy schedules (absolute times), then converted to offsets relative to 09:00
nancy_busy_abs = {
    0: [("10:00","10:30"), ("11:30","12:30"), ("13:30","14:00"),
        ("14:30","15:30"), ("16:00","17:00")],  # Monday
    1: [("09:30","10:30"), ("11:00","11:30"), ("12:00","12:30"),
        ("13:00","13:30"), ("15:30","16:00")],  # Tuesday
    2: [("10:00","11:30"), ("13:30","16:00")]   # Wednesday
}
jose_busy_abs = {
    0: [("09:00","17:00")],  # Monday
    1: [("09:00","17:00")],  # Tuesday
    2: [("09:00","09:30"), ("10:00","12:30"), ("13:30","14:30"), ("15:00","17:00")]  # Wednesday
}

def to_offsets(busy_abs):
    busy_off = {}
    for d, intervals in busy_abs.items():
        busy_off[d] = [(offset(s), offset(e)) for (s, e) in intervals]
    return busy_off

nancy_busy = to_offsets(nancy_busy_abs)
jose_busy = to_offsets(jose_busy_abs)

# Z3 model
opt = Optimize()

day = Int("day")       # 0=Mon, 1=Tue, 2=Wed
start = Int("start")   # offset in minutes from 09:00

# Domain constraints
opt.add(And(day >= 0, day <= 2))
opt.add(And(start >= 0, start <= (WORK_END - WORK_START - DURATION)))

# No overlap with busy intervals (use half-open intervals [start, end))
def no_overlap_with(busy_dict):
    constraints = []
    for d in [0, 1, 2]:
        for (bs, be) in busy_dict.get(d, []):
            constraints.append(Implies(day == d, Or(start + DURATION <= bs, start >= be)))
    return constraints

opt.add(no_overlap_with(nancy_busy))
opt.add(no_overlap_with(jose_busy))

# Earliest availability: minimize day, then start time
opt.minimize(day)
opt.minimize(start)

# Solve
if opt.check() !=  sat:
    # As per problem statement, a solution exists; this is just a safeguard.
    raise RuntimeError("No feasible schedule found")

m = opt.model()
chosen_day = m[day].as_long()
start_offset = m[start].as_long()
end_offset = start_offset + DURATION

start_time_abs = WORK_START + start_offset
end_time_abs = WORK_START + end_offset

print("SOLUTION:")
print(f"Day: {DAY_NAMES[chosen_day]}")
print(f"Start Time: {fmt_hhmm(start_time_abs)}")
print(f"End Time: {fmt_hhmm(end_time_abs)}")