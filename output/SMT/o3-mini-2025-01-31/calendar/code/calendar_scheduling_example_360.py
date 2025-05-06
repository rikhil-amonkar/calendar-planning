from z3 import Optimize, Int, Or, sat

# Helper functions to convert time strings to minutes and vice versa.
def time_to_minutes(t):
    # t is expected to be in the format "HH:MM"
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # minutes
work_start = time_to_minutes("9:00")   # 9:00 AM -> 540 minutes
work_end   = time_to_minutes("17:00")   # 5:00 PM -> 1020 minutes

# Busy intervals for each participant on Monday.
# All times are in minutes since midnight.
# Emily's busy intervals.
emily_busy = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Mason is free the entire day, so no busy intervals.
mason_busy = []

# Maria's busy intervals.
maria_busy = [
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("14:00"), time_to_minutes("14:30"))
]

# Carl's busy intervals.
carl_busy = [
    (time_to_minutes("9:30"),  time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("12:30")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

# David's busy intervals.
david_busy = [
    (time_to_minutes("9:30"),  time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("15:00")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

# Frank's busy intervals.
frank_busy = [
    (time_to_minutes("9:30"),  time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("17:00"))
]

# Combine all busy intervals in a list for ease of iterating.
all_busy = [emily_busy, mason_busy, maria_busy, carl_busy, david_busy, frank_busy]

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variable: meeting_start time in minutes from midnight on Monday.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting to be within the work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Function to add constraints that ensure the meeting does not conflict with a set of busy intervals.
def add_busy_constraints(busy_intervals):
    for (b_start, b_end) in busy_intervals:
        # The meeting must either finish before the busy interval starts or start after it ends.
        opt.add(Or(meeting_end <= b_start, meeting_start >= b_end))

# Add constraints for each participant.
for busy in all_busy:
    add_busy_constraints(busy)

# Objective: Choose the earliest available meeting time.
opt.minimize(meeting_start)

# Check for a solution and print the meeting time.
if opt.check() == sat:
    model = opt.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_time))
    print("End:  ", minutes_to_time(end_time))
else:
    print("No valid meeting time could be found.")