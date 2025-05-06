from z3 import Optimize, Int, Or, sat

# Helper functions to convert between time strings and minutes after midnight.
def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # in minutes
work_start = time_to_minutes("9:00")
work_end   = time_to_minutes("17:00")

# Bobby's preference: no meetings after 15:00.
# That means the meeting must end by 15:00.
bobby_latest_end = time_to_minutes("15:00")

# Busy intervals (in minutes) on Monday for each participant.

# Lisa's busy intervals:
lisa_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Bobby's busy intervals:
bobby_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("15:00"), time_to_minutes("15:30"))
]

# Randy's busy intervals:
randy_busy = [
    (time_to_minutes("9:30"),  time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30")),
]

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variable: meeting_start in minutes from midnight on Monday.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Meeting must be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Respect Bobby's preference: the meeting must finish by 15:00.
opt.add(meeting_end <= bobby_latest_end)

# Function to add non-overlapping constraints for busy intervals.
def add_busy_constraints(busy_intervals):
    for b_start, b_end in busy_intervals:
        # Meeting must end before a busy interval starts or start after it ends.
        opt.add(Or(meeting_end <= b_start, meeting_start >= b_end))

# Add constraints from each participant.
add_busy_constraints(lisa_busy)
add_busy_constraints(bobby_busy)
add_busy_constraints(randy_busy)

# Objective: choose the earliest available meeting time.
opt.minimize(meeting_start)

# Find and print a solution.
if opt.check() == sat:
    model = opt.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")