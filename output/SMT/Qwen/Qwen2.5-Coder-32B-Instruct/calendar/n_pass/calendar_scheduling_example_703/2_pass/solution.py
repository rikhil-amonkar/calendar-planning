from z3 import *

# Define the variables for the day and time
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constants for the days and time limits
MONDAY, TUESDAY, WEDNESDAY = 0, 1, 2
WORK_START = 9 * 60  # 9:00 in minutes
WORK_END = 17 * 60  # 17:00 in minutes
MEETING_DURATION = 60  # 1 hour in minutes

# Create a solver instance
solver = Solver()

# Constraints for the day
solver.add(day >= MONDAY)
solver.add(day <= WEDNESDAY)

# Constraints for the start time
solver.add(start_time >= WORK_START)
solver.add(start_time + MEETING_DURATION <= WORK_END)

# Stephanie's constraints
stephanie_meetings = [
    (MONDAY, 9*60+30, 10*60),
    (MONDAY, 10*60+30, 11*60),
    (MONDAY, 11*60+30, 12*60),
    (MONDAY, 14*60, 14*60+30),
    (TUESDAY, 12*60, 13*60),
    (WEDNESDAY, 9*60, 10*60),
    (WEDNESDAY, 13*60, 14*60)
]

for d, s, e in stephanie_meetings:
    solver.add(Or(day != d, Or(start_time + MEETING_DURATION <= s, start_time >= e)))

# Betty's constraints
betty_meetings = [
    (MONDAY, 9*60, 10*60),
    (MONDAY, 11*60, 11*60+30),
    (MONDAY, 14*60+30, 15*60),
    (MONDAY, 15*60+30, 16*60),
    (TUESDAY, 9*60, 9*60+30),
    (TUESDAY, 11*60+30, 12*60),
    (TUESDAY, 12*60+30, 14*60+30),
    (TUESDAY, 15*60+30, 16*60),
    (WEDNESDAY, 10*60, 11*60+30),
    (WEDNESDAY, 12*60, 14*60),
    (WEDNESDAY, 14*60+30, 17*60)
]

for d, s, e in betty_meetings:
    solver.add(Or(day != d, Or(start_time + MEETING_DURATION <= s, start_time >= e)))

# Additional constraints based on preferences
solver.add(day != MONDAY)  # Stephanie would like to avoid more meetings on Monday
solver.add(Or(day != TUESDAY, start_time + MEETING_DURATION <= 12*60+30))  # Betty can not meet on Tuesday after 12:30

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + MEETING_DURATION
    
    day_str = ["Monday", "Tuesday", "Wednesday"][day_value]
    start_time_str = f"{start_time_value // 60:02}:{start_time_value % 60:02}"
    end_time_str = f"{end_time_value // 60:02}:{end_time_value % 60:02}"
    
    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")