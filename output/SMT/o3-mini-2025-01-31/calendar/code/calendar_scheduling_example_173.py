from z3 import Optimize, Int, Or, If, sat

# Helper functions to convert between time strings and minutes.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # minutes
work_start = time_to_minutes("9:00")   # 540 minutes
work_end   = time_to_minutes("17:00")   # 1020 minutes

# For this task, the meeting is only on Monday. We'll encode Monday as day 0.
meeting_day_val = 0

# Busy intervals on Monday for each participant.

# Jacqueline busy intervals.
jacqueline_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

# Harold busy intervals.
harold_busy = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("15:00"), time_to_minutes("17:00"))
]

# Arthur busy intervals.
arthur_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("12:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("17:00"))
]

# Kelly busy intervals.
kelly_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:30")),
    (time_to_minutes("14:00"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variable: meeting_start time in minutes from midnight.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain meeting to be within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Harold does not want meetings on Monday after 13:00.
# Since the meeting is on Monday, enforce that the meeting ends before or at 13:00.
opt.add(meeting_end <= time_to_minutes("13:00"))

# Function to add non-overlap constraints for busy intervals.
def add_busy_constraints(busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting must either finish before a busy interval starts,
        # or start after the busy interval ends.
        opt.add(Or(meeting_end <= b_start, meeting_start >= b_end))

# Add busy constraints for all participants.
add_busy_constraints(jacqueline_busy)
add_busy_constraints(harold_busy)
add_busy_constraints(arthur_busy)
add_busy_constraints(kelly_busy)

# Objective: choose the earliest available meeting time.
# We minimize the meeting_start time.
opt.minimize(meeting_start)

# Solve for a meeting time.
if opt.check() == sat:
    model = opt.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")