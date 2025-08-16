from z3 import Solver, Int, Or

# Helper function to convert minutes-after-midnight to HH:MM string format
def minutes_to_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

# Create a Z3 solver instance
solver = Solver()

# Define the meeting duration in minutes and a variable for the meeting start time
duration = 30
meeting_start = Int("meeting_start")

# Work hours: Meeting can start at 9:00 (540 minutes) and must end by 17:00 (1020 minutes).
solver.add(meeting_start >= 9 * 60, meeting_start + duration <= 17 * 60)

# Define the busy intervals for each participant (in minutes after midnight)
# For example, 11:30 is 11*60+30 = 690 and 12:00 is 720.
busy_intervals = [
    # John
    (11 * 60 + 30, 12 * 60),    # 11:30 - 12:00
    (14 * 60, 14 * 60 + 30),     # 14:00 - 14:30
    # Megan
    (12 * 60, 12 * 60 + 30),     # 12:00 - 12:30
    (14 * 60, 15 * 60),          # 14:00 - 15:00
    (15 * 60 + 30, 16 * 60),     # 15:30 - 16:00
    # Brandon has no meetings, so no intervals here.
    # Kimberly
    (9 * 60, 9 * 60 + 30),       # 9:00 - 9:30
    (10 * 60, 10 * 60 + 30),     # 10:00 - 10:30
    (11 * 60, 14 * 60 + 30),     # 11:00 - 14:30
    (15 * 60, 16 * 60),          # 15:00 - 16:00
    (16 * 60 + 30, 17 * 60),     # 16:30 - 17:00
    # Sean
    (10 * 60, 11 * 60),          # 10:00 - 11:00
    (11 * 60 + 30, 14 * 60),     # 11:30 - 14:00
    (15 * 60, 15 * 60 + 30),     # 15:00 - 15:30
    # Lori
    (9 * 60, 9 * 60 + 30),       # 9:00 - 9:30
    (10 * 60 + 30, 12 * 60),     # 10:30 - 12:00
    (13 * 60, 14 * 60 + 30),     # 13:00 - 14:30
    (16 * 60, 16 * 60 + 30)      # 16:00 - 16:30
]

# For each busy interval, add a constraint that the scheduled meeting should not overlap.
# Two intervals [start1, end1) and [start2, end2) don't overlap if either:
#   meeting_end <= busy_start   or   meeting_start >= busy_end.
for (busy_start, busy_end) in busy_intervals:
    solver.add(Or(meeting_start + duration <= busy_start, meeting_start >= busy_end))

# Attempt to find a solution that satisfies all constraints.
if solver.check().r == 1:  # sat check
    model = solver.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + duration

    # Print the solution in the required format.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: " + minutes_to_str(start_time))
    print("End Time: " + minutes_to_str(end_time))
else:
    print("No solution found")