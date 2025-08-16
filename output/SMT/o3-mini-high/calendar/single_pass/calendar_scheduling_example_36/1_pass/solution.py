from z3 import *

# We'll represent times in minutes from midnight.
# For example, 9:00 is 9*60 = 540 and 17:00 is 17*60 = 1020.
# The meeting length is 60 minutes.
meeting_start = Int("meeting_start")
meeting_duration = 60
meeting_end = meeting_start + meeting_duration

# Create a Z3 solver instance.
solver = Solver()

# Constraint: The meeting must be within work hours 9:00 to 17:00.
solver.add(meeting_start >= 9*60)        # start >= 540
solver.add(meeting_end <= 17*60)          # end <= 1020

# Ryan's busy intervals on Monday:
#   9:00 to 9:30  -> [540, 570]
#  12:30 to 13:00 -> [750, 780]
# To avoid overlap, the meeting interval must be completely before or after each busy interval.
solver.add(Or(meeting_end <= 540, meeting_start >= 570))   # Avoid Ryan's 9:00-9:30
solver.add(Or(meeting_end <= 750, meeting_start >= 780))   # Avoid Ryan's 12:30-13:00

# Denise's busy intervals on Monday:
#   9:30 to 10:30 -> [570, 630]
#  12:00 to 13:00 -> [720, 780]
#  14:30 to 16:30 -> [870, 990]
solver.add(Or(meeting_end <= 570, meeting_start >= 630))   # Avoid Denise's 9:30-10:30
solver.add(Or(meeting_end <= 720, meeting_start >= 780))   # Avoid Denise's 12:00-13:00
solver.add(Or(meeting_end <= 870, meeting_start >= 990))   # Avoid Denise's 14:30-16:30

# Denise's preference: "do not want to meet on Monday after 12:30"
# We interpret this as the meeting must finish by 12:30, i.e. meeting_end <= 12:30 (750 minutes).
solver.add(meeting_end <= 750)

# Ruth has no meetings scheduled, so no additional constraints are needed for her.

# Try to solve all constraints.
if solver.check() == sat:
    model = solver.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration

    # Helper function to convert minutes to HH:MM (24-hour format)
    def to_time_str(minutes):
        hour = minutes // 60
        minute = minutes % 60
        return f"{hour:02d}:{minute:02d}"

    # Print the solution in the required format.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: " + to_time_str(start_val))
    print("End Time: " + to_time_str(end_val))
else:
    print("No solution found.")