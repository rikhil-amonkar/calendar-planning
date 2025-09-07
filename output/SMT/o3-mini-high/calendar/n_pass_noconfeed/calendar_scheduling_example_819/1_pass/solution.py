from z3 import *

def minutes_to_time(offset):
    # Given an offset in minutes from 9:00, convert to HH:MM format.
    total_minutes = 9 * 60 + offset
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Create a Z3 solver
solver = Solver()

# Let's represent the day as an integer:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday
day = Int('day')
solver.add(Or(day == 0, day == 1, day == 2, day == 3))

# Meeting start time in minutes after 9:00. 
# Since meeting lasts 30 minutes and work ends at 17:00 (480 minutes after 9:00),
# we require start ∈ [0, 450]
start = Int('start')
solver.add(start >= 0, start <= 450)

# -------------------------------------------------------
# Participant constraints:
# Julie: completely free, but she prefers to avoid meetings on Thursday before 11:30.
# Ruth: busy according to:
#   - Monday: 9:00-17:00 (i.e. entire day busy)
#   - Tuesday: 9:00-17:00
#   - Wednesday: 9:00-17:00
#   - Thursday: busy intervals:
#            9:00-11:00   --> offset [0, 120)
#           11:30-14:30   --> offset [150, 330)
#           15:00-17:00   --> offset [360, 480)
#
# The meeting duration is 30 minutes.
#
# Since Monday, Tuesday and Wednesday are fully busy for Ruth, the only possible day is Thursday.
solver.add(day == 3)

# Now apply Julie's preference for Thursday: if day is Thursday then meeting should not start before 11:30.
# 11:30 corresponds to an offset of 150 minutes (from 9:00).
solver.add(start >= 150)

# For Thursday, Ruth is busy in several chunks.
# Our meeting [start, start+30) must not overlap any busy intervals.
# Because start >= 150 (i.e. not before 11:30), the morning free window (11:00-11:30)
# is ruled out by Julie's preference.
#
# The only remaining free slot on Thursday for Ruth is from 14:30 to 15:00.
# 14:30 corresponds to an offset of 330 minutes and 15:00 corresponds to 360 minutes.
solver.add(start >= 330, start + 30 <= 360)

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = start_val + 30
    
    # Define day mapping for output.
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    chosen_day = day_names[day_val]
    
    # Convert offsets to actual time strings.
    start_time = minutes_to_time(start_val)
    end_time = minutes_to_time(end_val)
    
    # Output in the format: Day HH:MM:HH:MM (start time and end time)
    print(f"{chosen_day} {start_time}:{end_time}")
else:
    print("No solution found.")