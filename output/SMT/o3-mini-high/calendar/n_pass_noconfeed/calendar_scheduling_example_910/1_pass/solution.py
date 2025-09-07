from z3 import *

# Define the days of the week
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Create a Z3 solver instance
s = Solver()

# We'll represent the meeting by two integer variables:
# day ∈ {0,1,2,3,4} where 0=Monday, 1=Tuesday, ..., 4=Friday.
# start is the meeting start time in minutes after 9:00.
day = Int('day')
start = Int('start')
duration = 60  # Meeting duration in minutes

# Work hours are from 9:00 to 17:00 i.e., 0 to 480 minutes.
s.add(day >= 0, day <= 4)
s.add(start >= 0, start + duration <= 480)

# Busy intervals for each participant are expressed as:
# (day_index, busy_start, busy_end) where times are in minutes after 9:00.
busy_intervals = [
    # Bryan's busy intervals:
    (3, 30, 60),      # Thursday 9:30-10:00
    (3, 210, 240),    # Thursday 12:30-13:00
    (4, 90, 120),     # Friday 10:30-11:00
    (4, 300, 330),    # Friday 14:00-14:30

    # Nicholas' busy intervals:
    (0, 150, 180),    # Monday 11:30-12:00
    (0, 240, 390),    # Monday 13:00-15:30
    (1, 0, 30),       # Tuesday 9:00-9:30
    (1, 120, 270),    # Tuesday 11:00-13:30
    (1, 300, 450),    # Tuesday 14:00-16:30
    (2, 0, 30),       # Wednesday 9:00-9:30
    (2, 60, 120),     # Wednesday 10:00-11:00
    (2, 150, 270),    # Wednesday 11:30-13:30
    (2, 300, 330),    # Wednesday 14:00-14:30
    (2, 360, 450),    # Wednesday 15:00-16:30
    (3, 90, 150),     # Thursday 10:30-11:30
    (3, 180, 210),    # Thursday 12:00-12:30
    (3, 360, 390),    # Thursday 15:00-15:30
    (3, 450, 480),    # Thursday 16:30-17:00
    (4, 0, 90),       # Friday 9:00-10:30 (Nicholas)
    (4, 120, 180),    # Friday 11:00-12:00 (Nicholas)
    (4, 210, 330),    # Friday 12:30-14:30 (Nicholas)
    (4, 390, 420),    # Friday 15:30-16:00 (Nicholas)
    (4, 450, 480)     # Friday 16:30-17:00 (Nicholas)
]

# For each busy interval, if the meeting is scheduled on that day then its time must not overlap.
# Two intervals [A,B] and [C,D] do not overlap if either B <= C or A >= D.
for (d, b_start, b_end) in busy_intervals:
    s.add(Implies(day == d, Or(start + duration <= b_start, start >= b_end)))

# Add preference constraints:
# Bryan would like to avoid Tuesday → day != 1.
s.add(day != 1)
# Nicholas would rather not meet on Monday or Thursday → day != 0 and day != 3.
s.add(day != 0, day != 3)

# Check for a solution.
if s.check() == sat:
    m = s.model()
    chosen_day = m[day].as_long()
    chosen_start = m[start].as_long()
    meeting_end = chosen_start + duration

    # Convert the minutes offset to actual clock times (starting at 9:00).
    start_hour = 9 + chosen_start // 60
    start_min = chosen_start % 60
    end_hour = 9 + meeting_end // 60
    end_min = meeting_end % 60

    day_str = days[chosen_day]
    # Print the result in the format: "Day HH:MM:HH:MM"
    print(f"{day_str} {start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}")
else:
    print("No solution found.")