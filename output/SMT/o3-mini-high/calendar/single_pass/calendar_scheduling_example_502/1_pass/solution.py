from z3 import Solver, Int, Or, sat

# Helper function to format minutes as HH:MM (24-hour format)
def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Meeting duration in minutes
duration = 30

# Define meeting start time (in minutes after midnight)
meeting_start = Int("meeting_start")

# Create a Z3 solver instance
s = Solver()

# Working hours constraints for Monday: meeting must be between 9:00 (540) and 17:00 (1020)
s.add(meeting_start >= 9 * 60)
s.add(meeting_start + duration <= 17 * 60)

# Jack's preference: avoid meetings on Monday after 12:30 (i.e. meeting must end by 12:30, which is 750)
s.add(meeting_start + duration <= 12 * 60 + 30)

# Define busy intervals (in minutes) for each participant on Monday

# Jack is busy at:
# 9:30-10:30, 11:00-11:30, 12:30-13:00, 14:00-14:30, 16:00-16:30
jack_busy = [
    (9 * 60 + 30, 10 * 60 + 30),
    (11 * 60, 11 * 60 + 30),
    (12 * 60 + 30, 13 * 60),
    (14 * 60, 14 * 60 + 30),
    (16 * 60, 16 * 60 + 30)
]

# Charlotte is busy at:
# 9:30-10:00, 10:30-12:00, 12:30-13:30, 14:00-16:00
charlotte_busy = [
    (9 * 60 + 30, 10 * 60),
    (10 * 60 + 30, 12 * 60),
    (12 * 60 + 30, 13 * 60 + 30),
    (14 * 60, 16 * 60)
]

# For each busy interval, ensure that the meeting does not overlap.
# That is, the meeting must either finish before the busy interval starts,
# or start after the busy interval ends.
for start, end in jack_busy:
    s.add(Or(meeting_start + duration <= start, meeting_start >= end))

for start, end in charlotte_busy:
    s.add(Or(meeting_start + duration <= start, meeting_start >= end))

# Check if the constraints are satisfiable and extract a solution if possible.
if s.check() == sat:
    model = s.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + duration
    # Format times into HH:MM format
    start_time_str = format_time(start_val)
    end_time_str = format_time(end_val)
    
    # Print the solution in the required format.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time:", start_time_str)
    print("End Time:", end_time_str)
else:
    print("No solution found.")