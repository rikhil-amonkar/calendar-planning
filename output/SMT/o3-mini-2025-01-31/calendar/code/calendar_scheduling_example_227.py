from z3 import Optimize, Int, Or, sat

# Helper functions to convert times between strings and minutes.
def time_to_minutes(t):
    # Converts a time string "HH:MM" to minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Converts minutes since midnight to a "HH:MM" time string.
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # half an hour meeting.
work_start = time_to_minutes("9:00")    # 9:00 AM → 540 minutes.
work_end   = time_to_minutes("17:00")    # 5:00 PM → 1020 minutes.

# Busy intervals on Monday.

# Natalie's calendar is wide open.
natalie_busy = []

# David's busy intervals and constraint: he doesn't want to meet before 14:00.
# Busy intervals: 11:30 to 12:00, 14:30 to 15:00.
david_busy = [
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00"))
]

# Douglas's busy intervals: 9:30 to 10:00, 11:30 to 12:00, 13:00 to 13:30, 14:30 to 15:00.
douglas_busy = [
    (time_to_minutes("9:30"),  time_to_minutes("10:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:00"))
]

# Ralph's busy intervals: 9:00 to 9:30, 10:00 to 11:00, 11:30 to 12:30,
# 13:30 to 15:00, 15:30 to 16:00, 16:30 to 17:00.
ralph_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:30")),
    (time_to_minutes("13:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Jordan's busy intervals: 9:00 to 10:00, 12:00 to 12:30, 13:00 to 13:30, 14:30 to 15:00, 15:30 to 17:00.
jordan_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("10:00")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("17:00"))
]

# Combine busy intervals for all participants (Natalie is free, so can be skipped).
busy_schedules = [david_busy, douglas_busy, ralph_busy, jordan_busy]

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variable: meeting_start in minutes since midnight on Monday.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting to be within the work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Enforce David's preference to not meet before 14:00.
opt.add(meeting_start >= time_to_minutes("14:00"))

# For each busy interval, ensure the meeting does not overlap.
def add_busy_constraints(busy_intervals):
    for start_busy, end_busy in busy_intervals:
        opt.add(Or(meeting_end <= start_busy, meeting_start >= end_busy))

for busy in busy_schedules:
    add_busy_constraints(busy)

# Objective: choose the earliest available meeting start time.
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