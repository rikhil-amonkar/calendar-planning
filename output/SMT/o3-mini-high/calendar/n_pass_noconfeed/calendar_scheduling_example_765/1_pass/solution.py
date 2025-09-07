from z3 import *

# Convert minutes since midnight to a HH:MM string.
def minutes_to_str(m):
    h = m // 60
    mn = m % 60
    return f"{h:02d}:{mn:02d}"

# Create the Z3 solver.
s = Solver()

# Define meeting variables:
# meeting_day: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# meeting_start: start time in minutes from midnight.
meeting_day = Int('meeting_day')
meeting_start = Int('meeting_start')
meeting_duration = 30

# Constrain meeting_day to be one of {0,1,2} (Monday, Tuesday, Wednesday)
s.add(Or(meeting_day == 0, meeting_day == 1, meeting_day == 2))

# Working hours: 9:00 (540 minutes) to 17:00 (1020 minutes).
# The meeting must finish by 17:00 so meeting_start <= 1020 - meeting_duration = 990.
s.add(meeting_start >= 540, meeting_start <= 990)

# --------------------------
# Busy intervals are modeled as half-open intervals [start, end)
# A meeting [m, m+duration) does not conflict with a busy interval [b_start, b_end)
# if m+duration <= b_start or m >= b_end.
# --------------------------

# Participant: Joshua
# Monday: busy from 15:00 to 15:30 => [900, 930)
s.add(Implies(meeting_day == 0, Or(meeting_start + meeting_duration <= 900,
                                     meeting_start >= 930)))
# Tuesday: busy intervals:
#   [11:30,12:00] => [690, 720)
#   [13:00,13:30] => [780, 810)
#   [14:30,15:00] => [870, 900)
s.add(Implies(meeting_day == 1, Or(meeting_start + meeting_duration <= 690,
                                     meeting_start >= 720)))
s.add(Implies(meeting_day == 1, Or(meeting_start + meeting_duration <= 780,
                                     meeting_start >= 810)))
s.add(Implies(meeting_day == 1, Or(meeting_start + meeting_duration <= 870,
                                     meeting_start >= 900)))
# Wednesday: Joshua has no meetings.

# Participant: Joyce
# Monday: busy intervals:
#   [9:00, 9:30]   => [540, 570)
#   [10:00, 11:00] => [600, 660)
#   [11:30, 12:30] => [690, 750)
#   [13:00, 15:00] => [780, 900)
#   [15:30, 17:00] => [930, 1020)
s.add(Implies(meeting_day == 0, Or(meeting_start + meeting_duration <= 540,
                                     meeting_start >= 570)))
s.add(Implies(meeting_day == 0, Or(meeting_start + meeting_duration <= 600,
                                     meeting_start >= 660)))
s.add(Implies(meeting_day == 0, Or(meeting_start + meeting_duration <= 690,
                                     meeting_start >= 750)))
s.add(Implies(meeting_day == 0, Or(meeting_start + meeting_duration <= 780,
                                     meeting_start >= 900)))
s.add(Implies(meeting_day == 0, Or(meeting_start + meeting_duration <= 930,
                                     meeting_start >= 1020)))
# Tuesday: busy from 9:00 to 17:00 => [540, 1020)
s.add(Implies(meeting_day == 1, Or(meeting_start + meeting_duration <= 540,
                                     meeting_start >= 1020)))
# Wednesday: busy intervals:
#   [9:00, 9:30]   => [540, 570)
#   [10:00, 11:00] => [600, 660)
#   [12:30, 15:30] => [750, 930)
#   [16:00, 16:30] => [960, 990)
s.add(Implies(meeting_day == 2, Or(meeting_start + meeting_duration <= 540,
                                     meeting_start >= 570)))
s.add(Implies(meeting_day == 2, Or(meeting_start + meeting_duration <= 600,
                                     meeting_start >= 660)))
s.add(Implies(meeting_day == 2, Or(meeting_start + meeting_duration <= 750,
                                     meeting_start >= 930)))
s.add(Implies(meeting_day == 2, Or(meeting_start + meeting_duration <= 960,
                                     meeting_start >= 990)))

# Additional preference:
# "Joyce would rather not meet on Monday before 12:00" i.e., if Monday then meeting_start >= 720.
s.add(Implies(meeting_day == 0, meeting_start >= 720))

# Check if the constraints are satisfiable.
if s.check() == sat:
    m = s.model()
    day_val = m[meeting_day].as_long()
    start_val = m[meeting_start].as_long()
    end_val = start_val + meeting_duration
    
    # Map integer day to string.
    day_map = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    day_str = day_map[day_val]
    
    # Format the time range in HH:MM:HH:MM.
    time_range = f"{minutes_to_str(start_val)}:{minutes_to_str(end_val)}"
    
    print(day_str, f"{{{time_range}}}")
else:
    print("No solution found.")