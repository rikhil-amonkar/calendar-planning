from z3 import Optimize, Int, Or, If, sat

# Helper functions for time conversion.
def time_to_minutes(t):
    # Convert a time string "HH:MM" to minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Convert minutes since midnight back to a time string "HH:MM".
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # Half an hour meeting.
work_start = time_to_minutes("9:00")   # 9:00 AM -> 540 minutes.
work_end   = time_to_minutes("17:00")   # 5:00 PM -> 1020 minutes.

# Busy intervals on Monday for each participant.

# Ronald is free the entire day.
ronald_busy = []

# Stephen is busy on Monday during 10:00 to 10:30, 12:00 to 12:30.
stephen_busy = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30"))
]

# Brittany is busy on Monday during 11:00 to 11:30, 13:30 to 14:00, 15:30 to 16:00, 16:30 to 17:00.
brittany_busy = [
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Dorothy is busy on Monday during 9:00 to 9:30, 10:00 to 10:30, 11:00 to 12:30, 13:00 to 15:00, 15:30 to 17:00.
dorothy_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("17:00"))
]

# Rebecca is busy on Monday during 9:30 to 10:30, 11:00 to 11:30, 12:00 to 12:30, 13:00 to 17:00.
rebecca_busy = [
    (time_to_minutes("9:30"),  time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("17:00"))
]

# Jordan is busy on Monday during 9:00 to 9:30, 10:00 to 11:00, 11:30 to 12:00, 13:00 to 15:00, 15:30 to 16:30.
jordan_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:30"))
]

# Combine all busy schedules into a list for easy iteration.
all_busy = [ronald_busy, stephen_busy, brittany_busy, dorothy_busy, rebecca_busy, jordan_busy]

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variable: meeting_start (in minutes) on Monday.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting to be within the work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Function: For a given list of busy intervals, ensure the meeting does not overlap any.
def add_busy_constraints(busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting must either end on or before a busy interval starts,
        # or start on or after the busy interval ends.
        opt.add(Or(meeting_end <= b_start, meeting_start >= b_end))

# Add constraints from all participants.
for busy in all_busy:
    add_busy_constraints(busy)

# Objective: choose the earliest available meeting time.
opt.minimize(meeting_start)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_time))
    print("End:  ", minutes_to_time(end_time))
else:
    print("No valid meeting time could be found.")