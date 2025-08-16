from z3 import *

# Create a Z3 solver instance
solver = Solver()

# We represent the day as an integer: 0 = Monday, 1 = Tuesday.
day = Int('day')

# Represent the meeting start time in minutes from midnight.
# For example, 9:00 is 540 and 17:00 is 1020.
start = Int('start')
meeting_duration = 30  # meeting lasts 30 minutes

# Working hours constraint: meeting must start between 9:00 and 17:00 - duration.
solver.add(start >= 540, start <= 1020 - meeting_duration)

# Nathan cannot meet on Monday, so the meeting must be on Tuesday.
solver.add(day == 1)

# Amanda's Tuesday preference: she does not want to meet after 11:00.
# Thus, if the meeting is on Tuesday, it must finish by 11:00 (i.e. 660 minutes).
solver.add(Implies(day == 1, start + meeting_duration <= 660))

# Busy intervals must be avoided.
# For any busy interval [busy_start, busy_end], our meeting [start, start+30]
# must not overlap it; that is, we must have either:
#    meeting end <= busy_start   OR   meeting start >= busy_end.

# Amanda's busy intervals on Tuesday:
# Busy from 9:00 to 9:30 -> [540, 570]
solver.add(Implies(day == 1, Or(start + meeting_duration <= 540, start >= 570)))
# Busy from 10:00 to 10:30 -> [600, 630]
solver.add(Implies(day == 1, Or(start + meeting_duration <= 600, start >= 630)))

# Nathan's busy intervals on Tuesday:
# Busy from 9:00 to 10:30 -> [540, 630]
solver.add(Implies(day == 1, Or(start + meeting_duration <= 540, start >= 630)))

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = start_val + meeting_duration
    
    # Map integer day to string
    day_str = "Monday" if day_val == 0 else "Tuesday"
    
    # Format times in HH:MM format.
    start_time = "{:02d}:{:02d}".format(start_val // 60, start_val % 60)
    end_time = "{:02d}:{:02d}".format(end_val // 60, end_val % 60)
    
    print("SOLUTION:")
    print("Day: {}".format(day_str))
    print("Start Time: {}".format(start_time))
    print("End Time: {}".format(end_time))
else:
    print("No solution found")