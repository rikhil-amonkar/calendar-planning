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
solver.add(Or(
    Or(day != MONDAY, And(start_time < 9*60+30, start_time + MEETING_DURATION <= 9*60+30)),
    Or(day != MONDAY, And(start_time < 10*60+30, start_time + MEETING_DURATION <= 10*60+30)),
    Or(day != MONDAY, And(start_time < 11*60+30, start_time + MEETING_DURATION <= 11*60+30)),
    Or(day != MONDAY, And(start_time < 14*60, start_time + MEETING_DURATION <= 14*60)),
    Or(day != TUESDAY, And(start_time < 12*60, start_time + MEETING_DURATION <= 12*60)),
    Or(day != WEDNESDAY, And(start_time < 9*60, start_time + MEETING_DURATION <= 9*60)),
    Or(day != WEDNESDAY, And(start_time < 13*60, start_time + MEETING_DURATION <= 13*60))
))

# Betty's constraints
solver.add(Or(
    Or(day != MONDAY, And(start_time < 9*60, start_time + MEETING_DURATION <= 9*60)),
    Or(day != MONDAY, And(start_time < 11*60, start_time + MEETING_DURATION <= 11*60)),
    Or(day != MONDAY, And(start_time < 14*60+30, start_time + MEETING_DURATION <= 14*60+30)),
    Or(day != MONDAY, And(start_time < 15*60+30, start_time + MEETING_DURATION <= 15*60+30)),
    Or(day != TUESDAY, And(start_time < 9*60, start_time + MEETING_DURATION <= 9*60+30)),
    Or(day != TUESDAY, And(start_time < 11*60+30, start_time + MEETING_DURATION <= 11*60+30)),
    Or(day != TUESDAY, And(start_time < 12*60+30, start_time + MEETING_DURATION <= 12*60+30)),
    Or(day != TUESDAY, And(start_time < 15*60+30, start_time + MEETING_DURATION <= 15*60+30)),
    Or(day != WEDNESDAY, And(start_time < 10*60, start_time + MEETING_DURATION <= 10*60)),
    Or(day != WEDNESDAY, And(start_time < 12*60, start_time + MEETING_DURATION <= 12*60)),
    Or(day != WEDNESDAY, And(start_time < 14*60, start_time + MEETING_DURATION <= 14*60)),
    Or(day != WEDNESDAY, And(start_time < 14*60+30, start_time + MEETING_DURATION <= 14*60+30))
))

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