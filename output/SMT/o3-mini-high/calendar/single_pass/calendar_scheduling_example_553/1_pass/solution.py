from z3 import Int, Solver, Or

# Represent time in minutes from midnight.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes

s = Solver()

# Define meeting start time (in minutes) and meeting end time.
meeting_start = Int("meeting_start")
meeting_duration = 30
meeting_end = meeting_start + meeting_duration

# Constraint: meeting must be within work hours.
s.add(meeting_start >= 540)
s.add(meeting_end <= 1020)

# Preference: Henry would rather not meet after 10:00 (600 minutes)
# We'll enforce the meeting to finish by 10:00.
s.add(meeting_end <= 600)

# Define blocked intervals for each participant (times in minutes from midnight)
# Eric's blocked times on Monday.
eric_blocks = [
    (720, 780),   # 12:00 to 13:00
    (840, 900)    # 14:00 to 15:00
]

# Henry's blocked times on Monday.
henry_blocks = [
    (570, 600),   # 9:30 to 10:00
    (630, 660),   # 10:30 to 11:00
    (690, 750),   # 11:30 to 12:30
    (780, 810),   # 13:00 to 13:30
    (870, 900),   # 14:30 to 15:00
    (960, 1020)   # 16:00 to 17:00
]

# A helper function to ensure our meeting does not conflict with a blocked interval.
def non_overlap_constraint(block):
    block_start, block_end = block
    # The meeting must end before the block starts OR start after the block ends.
    return Or(meeting_end <= block_start, meeting_start >= block_end)

# Add constraints for Eric's busy times.
for block in eric_blocks:
    s.add(non_overlap_constraint(block))

# Add constraints for Henry's busy times.
for block in henry_blocks:
    s.add(non_overlap_constraint(block))

# Check if the constraints are satisfiable and print the solution.
if s.check() == "sat":
    m = s.model()
    start = m[meeting_start].as_long()
    end = start + meeting_duration

    # Helper function to format minutes into HH:MM format
    def format_time(total_minutes):
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    # Output the solution as required.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time:", format_time(start))
    print("End Time:", format_time(end))
else:
    print("No solution found.")