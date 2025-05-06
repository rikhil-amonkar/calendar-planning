from z3 import Optimize, Int, Or, sat

# Helper functions for time conversion.
def time_to_minutes(t):
    # Convert a time string "HH:MM" to minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Convert minutes since midnight to a time string "HH:MM".
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # 30-minute meeting.
work_start = time_to_minutes("9:00")   # 9:00 AM -> 540 minutes.
work_end   = time_to_minutes("17:00")   # 5:00 PM -> 1020 minutes.

# Busy intervals on Monday.

# Eric's busy intervals: 12:00-13:00, 14:00-15:00.
eric_busy = [
    (time_to_minutes("12:00"), time_to_minutes("13:00")),
    (time_to_minutes("14:00"), time_to_minutes("15:00"))
]

# Henry's busy intervals: 9:30-10:00, 10:30-11:00, 11:30-12:30, 13:00-13:30, 14:30-15:00, 16:00-17:00.
henry_busy = [
    (time_to_minutes("9:30"),  time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

# Create a Z3 Optimize solver.
opt = Optimize()

# Decision variable: meeting_start (in minutes since midnight on Monday).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting to be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Henry would rather not meet on Monday after 10:00.
opt.add(meeting_end <= time_to_minutes("10:00"))

# Function to add non-overlap constraints for busy intervals.
def add_busy_constraints(busy_intervals):
    for start_busy, end_busy in busy_intervals:
        # Meeting must end before the busy interval starts, or start after it ends.
        opt.add(Or(meeting_end <= start_busy, meeting_start >= end_busy))

# Add busy constraints for Eric and Henry.
add_busy_constraints(eric_busy)
add_busy_constraints(henry_busy)

# Objective: Schedule the meeting at the earliest available time.
opt.minimize(meeting_start)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    chosen_start = model[meeting_start].as_long()
    chosen_end = chosen_start + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(chosen_start))
    print("End:  ", minutes_to_time(chosen_end))
else:
    print("No valid meeting time could be found.")