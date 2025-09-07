from z3 import *

# Define S as the meeting start time (in minutes from midnight)
S = Int('S')

# Meeting duration is exactly 30 minutes (0.5 hours)
duration = 30  

# Create a solver instance and constrain the meeting to occur within working hours:
# starting no earlier than 9:00 (540 minutes) and finishing by 17:00 (1020 minutes)
solver = Solver()
solver.add(S >= 540, S + duration <= 1020)

# Busy intervals in minutes for each participant on Monday

# Patrick’s busy intervals:
#   9:00-9:30, 10:00-10:30, 13:30-14:00, 16:00-16:30
patrick_busy = [(540, 570), (600, 630), (810, 840), (960, 990)]

# Kayla’s busy intervals:
#   12:30-13:30, 15:00-15:30, 16:00-16:30
kayla_busy = [(750, 810), (900, 930), (960, 990)]

# Carl’s busy intervals:
#   10:30-11:00, 12:00-12:30, 13:00-13:30, 14:30-17:00
carl_busy = [(630, 660), (720, 750), (780, 810), (870, 1020)]

# Christian’s busy intervals:
#   9:00-12:30, 13:00-14:00, 14:30-17:00
christian_busy = [(540, 750), (780, 840), (870, 1020)]

# For each busy time interval, the meeting [S, S+duration] must either end 
# before the interval starts or begin after it ends.
def add_busy_constraints(busy_list):
    for (bstart, bend) in busy_list:
        solver.add(Or(S + duration <= bstart, S >= bend))

# Add constraints for all participants
add_busy_constraints(patrick_busy)
add_busy_constraints(kayla_busy)
add_busy_constraints(carl_busy)
add_busy_constraints(christian_busy)

# Check for a solution
if solver.check() == sat:
    m = solver.model()
    meeting_start = m[S].as_long()
    meeting_end = meeting_start + duration

    # Function to convert minutes to HH:MM string
    def format_time(minutes):
        hr = minutes // 60
        min_part = minutes % 60
        return f"{hr:02d}:{min_part:02d}"

    start_str = format_time(meeting_start)
    end_str = format_time(meeting_end)

    # Format the output as expected: a dictionary with day and time_range in curly braces.
    plan = {'day': 'Monday', 'time_range': f"{{{start_str}:{end_str}}}"}
    print(plan)
else:
    print("No solution found")