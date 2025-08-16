from z3 import *

# We represent times in minutes relative to 9:00.
# So 9:00 is 0 and 17:00 is 480 minutes.
# The meeting duration is 30 minutes.
duration = 30

# Create an integer variable for the meeting start time (in minutes since 9:00)
s = Int('s')

solver = Solver()

# The meeting must entirely occur during work hours: [9:00, 17:00]
solver.add(s >= 0)
solver.add(s + duration <= 480)

# Define the busy intervals for each participant (in minutes relative to 9:00):
# Andrea: free all day => no constraints.
# Jack busy: [9:00, 9:30] and [14:00, 14:30]
#   9:00 -> 0, 9:30 -> 30; 14:00 -> 300, 14:30 -> 330.
# Madison busy: [9:30, 10:30], [13:00, 14:00], [15:00, 15:30], [16:30, 17:00]
#   9:30 -> 30, 10:30 -> 90; 13:00 -> 240, 14:00 -> 300; 15:00 -> 360, 15:30 -> 390;
#   16:30 -> 450, 17:00 -> 480.
# Rachel busy: [9:30, 10:30], [11:00, 11:30], [12:00, 13:30], [14:30, 15:30], [16:00, 17:00]
#   9:30 -> 30, 10:30 -> 90; 11:00 -> 120, 11:30 -> 150; 12:00 -> 180, 13:30 -> 270;
#   14:30 -> 330, 15:30 -> 390; 16:00 -> 420, 17:00 -> 480.
# Douglas busy: [9:00, 11:30], [12:00, 16:30]
#   9:00 -> 0, 11:30 -> 150; 12:00 -> 180, 16:30 -> 450.
# Ryan busy: [9:00, 9:30], [13:00, 14:00], [14:30, 17:00]
#   9:00 -> 0, 9:30 -> 30; 13:00 -> 240, 14:00 -> 300; 14:30 -> 330, 17:00 -> 480.

busy_intervals = [
    # Jack's busy intervals:
    (0, 30), (300, 330),
    # Madison's busy intervals:
    (30, 90), (240, 300), (360, 390), (450, 480),
    # Rachel's busy intervals:
    (30, 90), (120, 150), (180, 270), (330, 390), (420, 480),
    # Douglas' busy intervals:
    (0, 150), (180, 450),
    # Ryan's busy intervals:
    (0, 30), (240, 300), (330, 480)
]

# For each busy interval [b_start, b_end],
# the meeting slot [s, s + duration] must not overlap with it.
# This non-overlap condition is: (s + duration <= b_start) OR (s >= b_end)
for b_start, b_end in busy_intervals:
    solver.add(Or(s + duration <= b_start, s >= b_end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[s].as_long()
    meeting_end = meeting_start + duration

    # Convert meeting_start and meeting_end to clock times (24-hour format).
    # Since 0 corresponds to 9:00, add 9 hours.
    start_hour = 9 + meeting_start // 60
    start_minute = meeting_start % 60
    end_hour = 9 + meeting_end // 60
    end_minute = meeting_end % 60

    # Print the solution in the required format.
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
    print(f"End Time: {end_hour:02d}:{end_minute:02d}")
else:
    print("No solution found")