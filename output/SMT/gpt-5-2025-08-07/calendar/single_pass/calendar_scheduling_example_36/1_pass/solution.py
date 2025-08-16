from z3 import Optimize, Int, Or

def minutes(h, m):
    return h * 60 + m

def hhmm(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

# Meeting parameters
work_start = minutes(9, 0)
work_end = minutes(17, 0)
duration = 60
day = "Monday"

# Busy intervals (start, end) in minutes since midnight, half-open [start, end)
ryan_busy = [
    (minutes(9, 0), minutes(9, 30)),
    (minutes(12, 30), minutes(13, 0)),
]
ruth_busy = []  # No meetings
denise_busy = [
    (minutes(9, 30), minutes(10, 30)),
    (minutes(12, 0), minutes(13, 0)),
    (minutes(14, 30), minutes(16, 30)),
]

# Preference: Denise does not want to meet after 12:30 -> meeting must end by 12:30
denise_end_by = minutes(12, 30)

# Z3 variables
start = Int("start")
end = Int("end")

opt = Optimize()

# Basic constraints: within work hours and fixed duration
opt.add(start >= work_start, end <= work_end, end - start == duration)

# No overlap with busy intervals
def add_no_overlap(intervals):
    for (b_start, b_end) in intervals:
        opt.add(Or(end <= b_start, start >= b_end))

add_no_overlap(ryan_busy)
add_no_overlap(ruth_busy)
add_no_overlap(denise_busy)

# Denise preference: meeting must end by 12:30
opt.add(end <= denise_end_by)

# Optional: find the earliest valid meeting start
opt.minimize(start)

if opt.check() == 1:  # sat
    model = opt.model()
    s_val = model.eval(start).as_long()
    e_val = model.eval(end).as_long()
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {hhmm(s_val)}")
    print(f"End Time: {hhmm(e_val)}")
else:
    # As per problem statement, a solution exists; this branch should not occur.
    # Included for completeness; would normally handle or raise an error.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: 00:00")
    print("End Time: 00:00")