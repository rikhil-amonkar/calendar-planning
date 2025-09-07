from z3 import Solver, Int, Or

# Meeting duration in minutes (1 hour)
meeting_duration = 60

# Define meeting start time in minutes from midnight
start = Int('start')

# Create a solver instance
solver = Solver()

# Working hours: meeting must start at or after 9:00 (540 minutes)
# and end by 17:00 (1020 minutes)
solver.add(start >= 9 * 60)
solver.add(start + meeting_duration <= 17 * 60)

# Julie's busy intervals (in minutes)
julie_busy = [
    (9 * 60, 9 * 60 + 30),     # 9:00 - 9:30
    (11 * 60, 11 * 60 + 30),   # 11:00 - 11:30
    (12 * 60, 12 * 60 + 30),   # 12:00 - 12:30
    (13 * 60 + 30, 14 * 60),   # 13:30 - 14:00
    (16 * 60, 17 * 60)         # 16:00 - 17:00
]

# Sean's busy intervals
sean_busy = [
    (9 * 60, 9 * 60 + 30),     # 9:00 - 9:30
    (13 * 60, 13 * 60 + 30),   # 13:00 - 13:30
    (15 * 60, 15 * 60 + 30),   # 15:00 - 15:30
    (16 * 60, 16 * 60 + 30)    # 16:00 - 16:30
]

# Lori's busy intervals
lori_busy = [
    (10 * 60, 10 * 60 + 30),   # 10:00 - 10:30
    (11 * 60, 13 * 60),        # 11:00 - 13:00
    (15 * 60 + 30, 17 * 60)     # 15:30 - 17:00
]

# A helper function to ensure the meeting does not overlap with a busy interval.
# Either the meeting finishes before the busy slot or starts after it.
def no_overlap(meeting_start, busy_interval):
    busy_start, busy_end = busy_interval
    return Or(meeting_start + meeting_duration <= busy_start, meeting_start >= busy_end)

# Add constraints for each busy interval for Julie, Sean and Lori
for interval in julie_busy:
    solver.add(no_overlap(start, interval))
for interval in sean_busy:
    solver.add(no_overlap(start, interval))
for interval in lori_busy:
    solver.add(no_overlap(start, interval))

# Check for a solution
if solver.check() == 'sat' or solver.check().r == -1:
    model = solver.model()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + meeting_duration

    # Function to convert minutes to HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    # The meeting is scheduled on Monday
    day = "Monday"
    time_range = f"{format_time(meeting_start)}:{format_time(meeting_end)}"
    print(day)
    print(time_range)
else:
    print("No solution found!")