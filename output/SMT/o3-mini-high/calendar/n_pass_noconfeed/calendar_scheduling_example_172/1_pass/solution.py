from z3 import *

# Define the meeting start time (in minutes from midnight)
S = Int('S')

# Create a solver instance
solver = Solver()

# Working hours: meeting must be scheduled between 9:00 (540 minutes) and 17:00 (1020 minutes)
# and the meeting lasts 30 minutes; hence, S + 30 <= 1020.
solver.add(S >= 540, S + 30 <= 1020)

duration = 30  # meeting duration in minutes

# Define busy intervals for each participant as (start_minute, end_minute)

# Patrick's busy intervals on Monday:
# 9:00-9:30, 10:00-10:30, 13:30-14:00, 16:00-16:30
patrick_busy = [(540, 570), (600, 630), (810, 840), (960, 990)]

# Kayla's busy intervals on Monday:
# 12:30-13:30, 15:00-15:30, 16:00-16:30
kayla_busy = [(750, 810), (900, 930), (960, 990)]

# Carl's busy intervals on Monday:
# 10:30-11:00, 12:00-12:30, 13:00-13:30, 14:30-17:00
carl_busy = [(630, 660), (720, 750), (780, 810), (870, 1020)]

# Christian's busy intervals on Monday:
# 9:00-12:30, 13:00-14:00, 14:30-17:00
christian_busy = [(540, 750), (780, 840), (870, 1020)]

# For each busy interval, ensure that the meeting [S, S+duration] does not overlap.
# That is, for each interval (bstart, bend), the meeting must end no later than bstart
# or start no earlier than bend.
def add_busy_constraints(busy_list):
    for (bstart, bend) in busy_list:
        solver.add(Or(S + duration <= bstart, S >= bend))

add_busy_constraints(patrick_busy)
add_busy_constraints(kayla_busy)
add_busy_constraints(carl_busy)
add_busy_constraints(christian_busy)

# Check for a solution
if solver.check() == sat:
    m = solver.model()
    meeting_start = m[S].as_long()
    meeting_end = meeting_start + duration

    # Convert minutes to HH:MM format
    def format_time(minutes):
        hr = minutes // 60
        min_part = minutes % 60
        return f"{hr:02d}:{min_part:02d}"

    start_str = format_time(meeting_start)
    end_str = format_time(meeting_end)
    # Output day and time range in the format: Day HH:MM:HH:MM
    print("Monday", f"{start_str}:{end_str}")
else:
    print("No solution found")