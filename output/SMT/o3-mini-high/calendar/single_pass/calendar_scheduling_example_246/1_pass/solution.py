from z3 import *

# Create a solver instance
s = Solver()

# Define an integer variable "start" representing the meeting start time in minutes after 9:00.
# The meeting duration is 30 minutes.
start = Int('start')
meeting_duration = 30

# The meeting must be scheduled within working hours (9:00 to 17:00).
# 9:00 corresponds to 0 minutes and 17:00 corresponds to 480 minutes after 9:00.
s.add(start >= 0, start + meeting_duration <= 480)

# Busy intervals (in minutes after 9:00) for each participant:

# Jacob is busy: 13:30 to 14:00 and 14:30 to 15:00.
jacob_busy = [(270, 300), (330, 360)]

# Diana is busy: 9:30 to 10:00, 11:30 to 12:00, 13:00 to 13:30, 16:00 to 16:30.
diana_busy = [(30, 60), (150, 180), (240, 270), (420, 450)]

# Adam is busy: 9:30 to 10:30, 11:00 to 12:30, 15:30 to 16:00.
adam_busy = [(30, 90), (120, 210), (390, 420)]

# Angela is busy: 9:30 to 10:00, 10:30 to 12:00, 13:00 to 15:30, 16:00 to 16:30.
angela_busy = [(30, 60), (90, 180), (240, 390), (420, 450)]

# Dennis is busy: 9:00 to 9:30, 10:30 to 11:30, 13:00 to 15:00, 16:30 to 17:00.
dennis_busy = [(0, 30), (90, 150), (240, 360), (450, 480)]

# A helper function to add the “no overlap” constraint for each busy interval.
# We model each busy slot as [busy_start, busy_end) and require that the meeting [start, start+30)
# does not intersect with it. That is, either the meeting ends on or before busy_start,
# or it starts on or after busy_end.
def add_busy_constraints(busy_intervals):
    for (b_start, b_end) in busy_intervals:
        s.add(Or(start + meeting_duration <= b_start, start >= b_end))

# Add constraints for each participant.
add_busy_constraints(jacob_busy)
add_busy_constraints(diana_busy)
add_busy_constraints(adam_busy)
add_busy_constraints(angela_busy)
add_busy_constraints(dennis_busy)

# Find a satisfying assignment
if s.check() == sat:
    m = s.model()
    meeting_start = m[start].as_long()
    meeting_end = meeting_start + meeting_duration

    # A helper function to convert minutes-since-9:00 into a time string (HH:MM) in 24-hour format.
    def minutes_to_time(x):
        total_minutes = 9 * 60 + x  # Add 9:00, which is 9*60 minutes.
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"

    day = "Monday"
    start_time_str = minutes_to_time(meeting_start)
    end_time_str = minutes_to_time(meeting_end)

    # Print the solution in the required format.
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")
else:
    print("No solution found")