from z3 import *

# Helper function to convert minutes offset from 9:00 to HH:MM (24-hour format)
def convert_minutes_to_time_str(offset):
    total_minutes = 9 * 60 + offset  # since 9:00 is our start of work day
    hour = total_minutes // 60
    minute = total_minutes % 60
    return f"{hour:02d}:{minute:02d}"

# Create solver instance
solver = Solver()

# Define variables:
# day: 0 = Monday, 1 = Tuesday, 2 = Wednesday
day = Int('day')
# start: meeting start time as minutes past 9:00. (Work hours: 9:00 to 17:00 -> 0 to 480 minutes)
start = Int('start')
duration = 30

# Working hours constraint: meeting must start between 9:00 and such that it ends by 17:00.
solver.add(start >= 0, start <= 480 - duration)
solver.add(Or(day == 0, day == 1, day == 2))

# Tyler's preference: He would like to avoid meetings on Monday before 16:00.
# 16:00 is 7 hours after 9:00, i.e. 7*60 = 420 minutes.
solver.add(Implies(day == 0, start >= 420))

# Define a helper for non-overlap:
# The meeting interval [start, start+duration] must not overlap a busy interval [b_start, b_end].
def no_overlap(start, b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

# Busy schedules for Tyler:
# On Tuesday, Tyler is busy during 9:00-9:30 ([0,30]) and 14:30-15:00 ([330,360]).
solver.add(Implies(day == 1, no_overlap(start, 0, 30)))
solver.add(Implies(day == 1, no_overlap(start, 330, 360)))
# On Wednesday, Tyler is busy during:
# 10:30-11:00 ([90,120]), 12:30-13:00 ([210,240]), 13:30-14:00 ([270,300]), and 16:30-17:00 ([450,480]).
solver.add(Implies(day == 2, no_overlap(start, 90, 120)))
solver.add(Implies(day == 2, no_overlap(start, 210, 240)))
solver.add(Implies(day == 2, no_overlap(start, 270, 300)))
solver.add(Implies(day == 2, no_overlap(start, 450, 480)))

# Busy schedules for Ruth:
# On Monday, Ruth is busy during:
# 9:00-10:00 ([0,60]), 10:30-12:00 ([90,180]), 12:30-14:30 ([150,330]),
# 15:00-16:00 ([360,420]), and 16:30-17:00 ([450,480]).
solver.add(Implies(day == 0, no_overlap(start, 0, 60)))
solver.add(Implies(day == 0, no_overlap(start, 90, 180)))
solver.add(Implies(day == 0, no_overlap(start, 150, 330)))
solver.add(Implies(day == 0, no_overlap(start, 360, 420)))
solver.add(Implies(day == 0, no_overlap(start, 450, 480)))
# On Tuesday, Ruth is busy the entire day from 9:00 to 17:00 ([0,480]).
solver.add(Implies(day == 1, no_overlap(start, 0, 480)))
# On Wednesday, Ruth is busy the entire day from 9:00 to 17:00 ([0,480]).
solver.add(Implies(day == 2, no_overlap(start, 0, 480)))

# Check if the constraints are satisfiable and extract a model
if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = start_val + duration
    
    # Map the numeric day to its name
    day_map = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    day_name = day_map[day_val]
    
    # Convert minute offsets to HH:MM format
    start_time_str = convert_minutes_to_time_str(start_val)
    end_time_str = convert_minutes_to_time_str(end_val)
    
    # Print the solution in the required format
    print("SOLUTION:")
    print("Day:", day_name)
    print("Start Time:", start_time_str)
    print("End Time:", end_time_str)
else:
    print("No solution found.")