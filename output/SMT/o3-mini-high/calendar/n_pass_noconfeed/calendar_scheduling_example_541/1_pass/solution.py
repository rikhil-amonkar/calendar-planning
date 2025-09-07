from z3 import Solver, Int, Or

# Create the Z3 solver instance
solver = Solver()

# Define the meeting start time (in minutes from midnight)
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# The meeting duration is 60 minutes, so the meeting must start no later than 17:00 - 60 = 16:00 (960 minutes)
s = Int('s')
duration = 60

# Domain constraint for the meeting start time
solver.add(s >= 540, s <= 960)

# ----------------------------
# Kayla's blocked intervals on Monday:
# 1. 10:00 to 10:30  (600 to 630 minutes)
# 2. 14:30 to 16:00  (870 to 960 minutes)
# The meeting [s, s+60] must not overlap with these intervals.
solver.add(Or(s + duration <= 600, s >= 630))   # Avoid conflict with 10:00 - 10:30
solver.add(Or(s + duration <= 870, s >= 960))   # Avoid conflict with 14:30 - 16:00

# ----------------------------
# Rebecca's blocked intervals on Monday:
# 1. 9:00 to 13:00   (540 to 780 minutes)
# 2. 13:30 to 15:00  (810 to 900 minutes)
# 3. 15:30 to 16:00  (930 to 960 minutes)
# The meeting [s, s+60] must not overlap with these intervals.
# For the first interval, since s is at least 540 anyway, we require s >= 780.
solver.add(s >= 780)                           # Meeting must start at or after 13:00

solver.add(Or(s + duration <= 810, s >= 900))   # Avoid conflict with 13:30 - 15:00
solver.add(Or(s + duration <= 930, s >= 960))   # Avoid conflict with 15:30 - 16:00

# Solve the constraints
if solver.check().r == 1:
    model = solver.model()
    start_time = model[s].as_long()
    end_time = start_time + duration

    # Convert the start and end times into HH:MM format
    def format_time(total_minutes):
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"

    meeting_start_str = format_time(start_time)
    meeting_end_str = format_time(end_time)

    # Define the meeting day (given in the problem: Monday)
    meeting_day = "Monday"

    # Output the results in the desired format: HH:MM:HH:MM and day of the week
    print(f"Meeting Time: {{{meeting_start_str}:{meeting_end_str}}}")
    print(f"Day: {meeting_day}")
else:
    print("No valid meeting time found.")