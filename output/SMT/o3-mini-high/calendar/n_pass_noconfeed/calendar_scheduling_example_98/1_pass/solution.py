from z3 import Solver, Int, Or

# Helper function to format minutes into HH:MM format
def format_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Create the solver
solver = Solver()

# Define the meeting start time (in minutes from midnight)
S = Int('S')
duration = 30

# Define work hours:
# Meeting must start no earlier than 9:00 (540 minutes) and, because Juan cannot meet after 16:00,
# the meeting must finish by 16:00 (960 minutes), so S+30 <= 960, i.e., S <= 930.
solver.add(S >= 540, S <= 930)

# Define a helper function that ensures the meeting does NOT overlap with a busy interval.
# A meeting [S, S+duration) does not overlap with busy interval [b_start, b_end) if either:
# the meeting ends on or before the busy period starts or it starts on or after the busy period ends.
def no_overlap(b_start, b_end):
    return Or(S + duration <= b_start, S >= b_end)

# Add busy intervals for each participant (times in minutes from midnight):

# Juan's busy times on Monday:
#   9:00 - 10:30  -> 540 to 630
#   15:30 - 16:00 -> 930 to 960
solver.add(no_overlap(540, 630))
solver.add(no_overlap(930, 960))

# Marilyn's busy times on Monday:
#   11:00 - 11:30 -> 660 to 690
#   12:30 - 13:00 -> 750 to 780
solver.add(no_overlap(660, 690))
solver.add(no_overlap(750, 780))

# Ronald's busy times on Monday:
#   9:00 - 10:30  -> 540 to 630
#   12:00 - 12:30 -> 720 to 750
#   13:00 - 13:30 -> 780 to 810
#   14:00 - 16:30 -> 840 to 990
solver.add(no_overlap(540, 630))
solver.add(no_overlap(720, 750))
solver.add(no_overlap(780, 810))
solver.add(no_overlap(840, 990))

# Solve the constraints
if solver.check() == 'sat' or solver.check() is not None:
    model = solver.model()
    start_time = model[S].as_long()
    end_time = start_time + duration
    # Output the meeting day (Monday) and the time range in the format HH:MM:HH:MM
    print("Monday " + format_time(start_time) + ":" + format_time(end_time))
else:
    print("No solution found.")