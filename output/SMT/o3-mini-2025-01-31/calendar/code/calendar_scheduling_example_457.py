from z3 import Optimize, Int, Or, sat

# Helper functions to convert time strings to minutes and vice versa.
def time_to_minutes(t):
    # Converts a time "HH:MM" into minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Converts minutes since midnight back to "HH:MM" format.
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # in minutes
work_start = time_to_minutes("9:00")   # 540 minutes
work_end   = time_to_minutes("17:00")   # 1020 minutes

# Busy intervals for each participant on Monday.
# Each tuple represents (start_time, end_time) in minutes.
# Andrea: 9:30-10:30 and 13:30-14:30.
andrea_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:30")),
    (time_to_minutes("13:30"), time_to_minutes("14:30"))
]

# Ruth: 12:30-13:00 and 15:00-15:30.
ruth_busy = [
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("15:00"), time_to_minutes("15:30"))
]

# Steven: 10:00-10:30, 11:00-11:30, 12:00-12:30, 13:30-14:00, 15:00-16:00.
steven_busy = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("15:00"), time_to_minutes("16:00"))
]

# Grace has no meetings.
grace_busy = []  # Free all day.

# Kyle: 9:00-9:30, 10:30-12:00, 12:30-13:00, 13:30-15:00, 15:30-16:00, 16:30-17:00.
kyle_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:30"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("13:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Elijah: 9:00-11:00, 11:30-13:00, 13:30-14:00, 15:30-16:00, 16:30-17:00.
elijah_busy = [
    (time_to_minutes("9:00"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("13:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Lori: 9:00-9:30, 10:00-11:30, 12:00-13:30, 14:00-16:00, 16:30-17:00.
lori_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Create an Optimize solver.
opt = Optimize()

# Decision variable: meeting start time in minutes (on Monday).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Meeting must be within working hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Function to add non-overlap constraints given busy intervals.
def add_busy_constraints(busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must either finish before a busy interval starts or start after it ends.
        opt.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# Add constraints for each participant.
add_busy_constraints(andrea_busy)
add_busy_constraints(ruth_busy)
add_busy_constraints(steven_busy)
add_busy_constraints(grace_busy)  # not needed, but here for completeness.
add_busy_constraints(kyle_busy)
add_busy_constraints(elijah_busy)
add_busy_constraints(lori_busy)

# Objective: Find the earliest available meeting time.
opt.minimize(meeting_start)

# Check for a valid meeting time.
if opt.check() == sat:
    model = opt.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")