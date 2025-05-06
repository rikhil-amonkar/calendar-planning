from z3 import Optimize, Int, Or, sat

# Helper functions to convert time strings to minutes and vice versa.
def time_to_minutes(t):
    # Convert "HH:MM" to minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Convert minutes since midnight back to "HH:MM".
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # 30-minute meeting.
work_start = time_to_minutes("9:00")   # 540 minutes.
work_end   = time_to_minutes("17:00")   # 1020 minutes.

# Samuel's busy intervals on Monday.
# Format: (start_time, end_time) in minutes.
samuel_busy = [
    (time_to_minutes("9:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Andrew and Grace are free all day, so no constraints are needed for them.

# Create an Optimize solver to minimize the meeting start time (earliest availability).
opt = Optimize()

# Decision variable: meeting start time in minutes (on Monday).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Meeting must occur within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Function to add constraints to ensure the meeting does not overlap with a busy interval.
def add_busy_constraints(busy_intervals):
    for b_start, b_end in busy_intervals:
        # Meeting must end before the busy interval starts or start after it ends.
        opt.add(Or(meeting_end <= b_start, meeting_start >= b_end))

# Add constraints for Samuel's busy intervals.
add_busy_constraints(samuel_busy)

# Objective: minimize the meeting start time to get the earliest possible time.
opt.minimize(meeting_start)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")