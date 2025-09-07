from z3 import *

def minutes(h, m=0):
    return h * 60 + m

def time_str(mins):
    return f"{mins//60:02d}:{mins%60:02d}"

# Meeting details
day = "Monday"
work_start = minutes(9, 0)
work_end = minutes(17, 0)
duration = 30  # minutes

# Busy schedules (as [start, end) intervals in minutes from 00:00)
adam_busy = [
    (minutes(14, 0), minutes(15, 0)),
]

john_busy = [
    (minutes(13, 0), minutes(13, 30)),
    (minutes(14, 0), minutes(14, 30)),
    (minutes(15, 30), minutes(16, 0)),
    (minutes(16, 30), minutes(17, 0)),
]

stephanie_busy = [
    (minutes(9, 30), minutes(10, 0)),
    (minutes(10, 30), minutes(11, 0)),
    (minutes(11, 30), minutes(16, 0)),
    (minutes(16, 30), minutes(17, 0)),
]

anna_busy = [
    (minutes(9, 30), minutes(10, 0)),
    (minutes(12, 0), minutes(12, 30)),
    (minutes(13, 0), minutes(15, 30)),
    (minutes(16, 30), minutes(17, 0)),
]

# Preference: Anna would rather not meet on Monday before 14:30 (treat as constraint)
anna_pref_start = minutes(14, 30)

# Z3 variables
start = Int('start')
end = Int('end')

s = Solver()

# Meeting duration and bounds within work hours
s.add(end == start + duration)
s.add(start >= work_start, end <= work_end)

# Anna's preference constraint
s.add(start >= anna_pref_start)

def add_no_overlap(busy_list):
    for (b_start, b_end) in busy_list:
        # No overlap: [start, end) does not intersect [b_start, b_end)
        s.add(Or(end <= b_start, start >= b_end))

# Apply no-overlap constraints for each participant
add_no_overlap(adam_busy)
add_no_overlap(john_busy)
add_no_overlap(stephanie_busy)
add_no_overlap(anna_busy)

if s.check() == sat:
    m = s.model()
    start_val = m[start].as_long()
    end_val = m[end].as_long()
    # Output includes both the day and the time range with braces, and the HH:MM:HH:MM format
    print(day)
    print(f"{{{time_str(start_val)}:{time_str(end_val)}}}")
    print(f"{time_str(start_val)}:{time_str(end_val)}")
else:
    print("No solution found.")