from z3 import *

# Represent time in minutes from midnight.
# Monday working hours: 9:00 (540) to 17:00 (1020)
# Meeting duration is 30 minutes.
# Bobby prefers that the meeting finish by 15:00 (900), so meeting must start no later than 870.

# Create the solver
solver = Solver()

# The meeting start time in minutes from midnight.
start = Int('start')
duration = 30
end = start + duration

# Add domain constraints:
# Meeting must start no earlier than 9:00 (540)
# And because Bobby wants the meeting before 15:00 (end <= 900), start must be <= 870.
solver.add(start >= 540, start <= 870)

# Define a helper function to enforce non-overlap with a busy interval.
# Two intervals [s, s+duration] and [busy_start, busy_end] do not overlap if:
#   meeting ends on or before busy_start OR meeting starts on or after busy_end.
def no_overlap(s, busy_start, busy_end):
    return Or(s + duration <= busy_start, s >= busy_end)

# Existing busy intervals for each participant (in minutes):
# Lisa's meetings: [9:00,10:00], [10:30,11:30], [12:30,13:00], [16:00,16:30]
lisa_busy = [(540, 600), (630, 690), (750, 780), (960, 990)]

# Bobby's meetings: [9:00,9:30], [10:00,10:30], [11:30,12:00], [15:00,15:30]
bobby_busy = [(540, 570), (600, 630), (690, 720), (900, 930)]

# Randy's meetings: [9:30,10:00], [10:30,11:00], [11:30,12:30], [13:00,13:30], [14:30,15:30], [16:00,16:30]
randy_busy = [(570, 600), (630, 660), (690, 750), (780, 810), (870, 930), (960, 990)]

# Add non-overlap constraints for Lisa
for b_start, b_end in lisa_busy:
    solver.add(no_overlap(start, b_start, b_end))

# Add non-overlap constraints for Bobby
for b_start, b_end in bobby_busy:
    solver.add(no_overlap(start, b_start, b_end))

# Add non-overlap constraints for Randy
for b_start, b_end in randy_busy:
    solver.add(no_overlap(start, b_start, b_end))

# Check if a solution exists and print it in the required format.
if solver.check() == sat:
    m = solver.model()
    meeting_start = m[start].as_long()
    meeting_end = meeting_start + duration

    # Helper function to convert minutes to HH:MM in 24-hour format.
    def minutes_to_HHMM(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: " + minutes_to_HHMM(meeting_start))
    print("End Time: " + minutes_to_HHMM(meeting_end))
else:
    print("No solution found.")