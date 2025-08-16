from z3 import Solver, Int, Or, And, sat

def to_minutes(h, m):
    return h * 60 + m

def fmt_minutes(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

# Meeting parameters
duration = 30  # minutes
work_start = to_minutes(9, 0)
work_end = to_minutes(17, 0)

# Busy schedules (start, end) in minutes since midnight
emily_busy = [
    (to_minutes(10, 0), to_minutes(10, 30)),
    (to_minutes(11, 30), to_minutes(12, 30)),
    (to_minutes(14, 0), to_minutes(15, 0)),
    (to_minutes(16, 0), to_minutes(16, 30)),
]

melissa_busy = [
    (to_minutes(9, 30), to_minutes(10, 0)),
    (to_minutes(14, 30), to_minutes(15, 0)),
]

frank_busy = [
    (to_minutes(10, 0), to_minutes(10, 30)),
    (to_minutes(11, 0), to_minutes(11, 30)),
    (to_minutes(12, 30), to_minutes(13, 0)),
    (to_minutes(13, 30), to_minutes(14, 30)),
    (to_minutes(15, 0), to_minutes(16, 0)),
    (to_minutes(16, 30), to_minutes(17, 0)),
]

# Frank does not want to meet on Monday after 9:30 => meeting must end by 09:30
frank_latest_end = to_minutes(9, 30)

# Z3 variables
start = Int('start')
end = Int('end')

s = Solver()

# Basic constraints
s.add(end == start + duration)
s.add(start >= work_start)
s.add(end <= work_end)

# Frank's preference: end by 09:30
s.add(end <= frank_latest_end)

# Non-overlapping constraints for each participant
def add_non_overlap(busy_list):
    for (bs, be) in busy_list:
        # Meeting does not overlap busy interval: end <= busy_start OR start >= busy_end
        s.add(Or(end <= bs, start >= be))

add_non_overlap(emily_busy)
add_non_overlap(melissa_busy)
add_non_overlap(frank_busy)

if s.check() == sat:
    m = s.model()
    start_time = m[start].as_long()
    end_time = m[end].as_long()
    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {fmt_minutes(start_time)}")
    print(f"End Time: {fmt_minutes(end_time)}")
else:
    print("No solution found.")