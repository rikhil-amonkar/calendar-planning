from z3 import *

# Meeting parameters
duration = 30  # minutes
work_start = 9 * 60   # 09:00 in minutes since 00:00
work_end   = 17 * 60  # 17:00 in minutes since 00:00
day = "Monday"

# Convert absolute times (HH:MM) to minutes since work_start (09:00)
def to_rel_minutes(h, m):
    return (h * 60 + m) - work_start

# Busy schedules as (start_rel_min, end_rel_min) half-open intervals [start, end)
# Emily busy:
emily_busy = [
    (to_rel_minutes(10, 0),  to_rel_minutes(10, 30)),
    (to_rel_minutes(11, 30), to_rel_minutes(12, 30)),
    (to_rel_minutes(14, 0),  to_rel_minutes(15, 0)),
    (to_rel_minutes(16, 0),  to_rel_minutes(16, 30)),
]

# Melissa busy:
melissa_busy = [
    (to_rel_minutes(9, 30),  to_rel_minutes(10, 0)),
    (to_rel_minutes(14, 30), to_rel_minutes(15, 0)),
]

# Frank busy:
frank_busy = [
    (to_rel_minutes(10, 0),  to_rel_minutes(10, 30)),
    (to_rel_minutes(11, 0),  to_rel_minutes(11, 30)),
    (to_rel_minutes(12, 30), to_rel_minutes(13, 0)),
    (to_rel_minutes(13, 30), to_rel_minutes(14, 30)),
    (to_rel_minutes(15, 0),  to_rel_minutes(16, 0)),
    (to_rel_minutes(16, 30), to_rel_minutes(17, 0)),
]

# Frank's preference: do not want to meet on Monday after 9:30
# Enforce that no part of the meeting is after 09:30 → meeting_end <= 09:30
frank_no_after_rel = to_rel_minutes(9, 30)  # 30 minutes after 09:00 → 30

# Z3 variables
start = Int('start')  # minutes relative to 09:00
end = start + duration

s = Solver()

# Working hours constraint
s.add(start >= 0)
s.add(end <= (work_end - work_start))

# No overlap constraints
def no_overlap(busy_intervals):
    return [Or(end <= b_start, start >= b_end) for (b_start, b_end) in busy_intervals]

s.add(no_overlap(emily_busy))
s.add(no_overlap(melissa_busy))
s.add(no_overlap(frank_busy))

# Frank's preference constraint
s.add(end <= frank_no_after_rel)

# Solve
if s.check() == sat:
    m = s.model()
    start_val = m[start].as_long()
    end_val = start_val + duration

    def fmt_time(rel_minutes):
        abs_minutes = work_start + rel_minutes
        hh = abs_minutes // 60
        mm = abs_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    start_str = fmt_time(start_val)
    end_str = fmt_time(end_val)

    print(f"{day} {{{start_str}:{end_str}}}")
else:
    print("No feasible time found.")