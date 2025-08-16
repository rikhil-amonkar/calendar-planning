from z3 import Optimize, Int, Or, sat

# Convert a time in "HH:MM" to minutes since midnight (not needed for this problem,
# but provided for clarity).
def to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

# Meeting length is 30 minutes.
meeting_duration = 30

# Define the meeting start time as an integer representing minutes since midnight.
# Working hours: 9:00 (540 minutes) to 17:00 (1020 minutes) on Monday.
start = Int('start')

# Create an Optimize object (to use the minimize capability)
solver = Optimize()
solver.add(start >= 540)               # Meeting cannot start before 9:00.
solver.add(start + meeting_duration <= 1020)  # Meeting must end by 17:00.

# Samuel's busy intervals on Monday (given in minutes since midnight):
# 9:00-10:30, 11:30-12:00, 13:00-13:30, 14:00-16:00, 16:30-17:00.
busy_intervals = [
    (540, 630),   # 9:00 to 10:30
    (690, 720),   # 11:30 to 12:00
    (780, 810),   # 13:00 to 13:30
    (840, 960),   # 14:00 to 16:00
    (990, 1020)   # 16:30 to 17:00
]

# For each busy interval, add a constraint ensuring the meeting does not overlap.
# The meeting [start, start + meeting_duration) must either finish before the busy interval
# starts or begin after the busy interval ends.
for (busy_start, busy_end) in busy_intervals:
    solver.add(Or(start + meeting_duration <= busy_start, start >= busy_end))

# The group would like to meet at their earliest availability.
# We minimize the meeting start time.
solver.minimize(start)

if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes since midnight back into "HH:MM" format.
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time:", minutes_to_time(meeting_start))
    print("End Time:", minutes_to_time(meeting_end))
else:
    print("No solution found.")