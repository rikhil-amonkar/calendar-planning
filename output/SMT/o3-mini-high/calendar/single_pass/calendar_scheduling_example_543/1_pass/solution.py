from z3 import *

# Define the meeting duration in minutes (1 hour)
duration = 60

# We model time as minutes past 9:00. The working day is 9:00 to 17:00, i.e. 0 to 480 minutes.
# The meeting must finish by 480 so the start time t must satisfy t + duration <= 480.
t = Int('t')

# Create the Z3 solver and add the domain constraint for t.
s = Solver()
s.add(t >= 0, t + duration <= 480)

# Busy intervals (in minutes relative to 9:00):
# James is busy:
#   11:30 - 12:00  => from (11-9)*60+30 = 150 to (12-9)*60 = 180
#   14:30 - 15:00  => from (14-9)*60+30 = 330 to (15-9)*60 = 360
# John is busy:
#   9:30 - 11:00   => from (9-9)*60+30 = 30  to (11-9)*60 = 120
#   11:30 - 12:00  => from 150 to 180
#   12:30 - 13:30  => from (12-9)*60+30 = 210 to (13-9)*60+30 = 270
#   14:30 - 16:30  => from 330 to (16-9)*60+30 = 450
busy_intervals = [
    (150, 180),  # James busy
    (330, 360),  # James busy
    (30, 120),   # John busy
    (150, 180),  # John busy
    (210, 270),  # John busy
    (330, 450)   # John busy
]

# For each busy interval, ensure that the meeting does not overlap.
# That is, for a busy interval [busy_start, busy_end],
# we require that either the meeting finishes before it starts (t + duration <= busy_start)
# OR it starts after the busy interval ends (t >= busy_end).
for busy_start, busy_end in busy_intervals:
    s.add(Or(t + duration <= busy_start, t >= busy_end))

# Solve the constraints.
if s.check() == sat:
    m = s.model()
    meeting_start = m[t].as_long()
    # Convert meeting start time (minutes from 9:00) into HH:MM format.
    start_hour = 9 + meeting_start // 60
    start_minute = meeting_start % 60

    meeting_end = meeting_start + duration
    end_hour = 9 + meeting_end // 60
    end_minute = meeting_end % 60

    # Print the solution in the required format.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: {:02d}:{:02d}".format(start_hour, start_minute))
    print("End Time: {:02d}:{:02d}".format(end_hour, end_minute))
else:
    print("No solution found.")