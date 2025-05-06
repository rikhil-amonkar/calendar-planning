from z3 import Optimize, Int, Or, sat

# Helper functions for converting time strings.
def time_to_minutes(time_str):
    # Converts a time string "HH:MM" to minutes since midnight.
    h, m = map(int, time_str.split(":"))
    return h * 60 + m

def minutes_to_time(minutes):
    # Converts minutes since midnight back to a "HH:MM" string.
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # meeting duration in minutes.
work_start = time_to_minutes("9:00")   # 9:00 => 540 minutes.
work_end = time_to_minutes("17:00")    # 17:00 => 1020 minutes.

# Busy intervals on Monday for each participant (in minutes):

# Michael's busy intervals:
# 9:30-10:30, 15:00-15:30, 16:00-16:30.
michael_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Eric's calendar is wide open: no constraints.
eric_busy = []  # No busy intervals.

# Arthur's busy intervals:
# 9:00-12:00, 13:00-15:00, 15:30-16:00, 16:30-17:00.
arthur_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Create a Z3 Optimize solver.
opt = Optimize()

# Decision variable: meeting start time (in minutes from midnight on Monday).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Ensure the meeting occurs within working hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Function to add non-overlapping constraints for busy intervals.
def add_busy_constraints(busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting must either end before a busy interval starts or start after it ends.
        opt.add(Or(meeting_end <= b_start, meeting_start >= b_end))

# Add constraints for Michael, Eric, and Arthur.
add_busy_constraints(michael_busy)
add_busy_constraints(eric_busy)   # Eric is free, so this effectively doesn't add constraints.
add_busy_constraints(arthur_busy)

# Objective: Minimize meeting start time for earliest scheduling.
opt.minimize(meeting_start)

# Check for a valid solution.
if opt.check() == sat:
    model = opt.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")