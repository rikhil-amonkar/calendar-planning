from z3 import Optimize, Int, Or

# Helper functions to convert time strings to minutes and vice versa.
def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # 30-minute meeting.
work_start = time_to_minutes("9:00")    # 540 minutes.
work_end   = time_to_minutes("17:00")   # 1020 minutes.

# Busy intervals for each participant on Monday, given as (start, end) in minutes.
lisa_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("14:00"), time_to_minutes("16:00"))
]

anthony_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Create an Optimize solver to minimize the meeting start time (earliest availability).
opt = Optimize()

# Define the meeting start time variable (in minutes).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint: Meeting must be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# For any busy interval [busy_start, busy_end], enforce that the meeting does not overlap:
# Either meeting_end is before or equal to busy_start, or meeting_start is after or equal to busy_end.
def add_busy_constraints(busy_intervals):
    for busy_start, busy_end in busy_intervals:
        opt.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# Add busy constraints for Lisa and Anthony.
add_busy_constraints(lisa_busy)
add_busy_constraints(anthony_busy)

# Objective: Schedule the meeting at the earliest possible start time.
opt.minimize(meeting_start)

# Check for a valid meeting time and print the result.
if opt.check() == sat:
    model = opt.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")