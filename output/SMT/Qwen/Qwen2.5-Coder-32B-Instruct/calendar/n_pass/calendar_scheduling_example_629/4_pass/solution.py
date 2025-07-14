from z3 import *

# Define variables
day = Int('day')  # 1 for Monday, 2 for Tuesday
start_time = Int('start_time')  # in minutes from 9:00

# Constants for time conversion
nine_am = 0  # 9:00 in minutes from 9:00
half_hour = 30  # Meeting duration in minutes

# Define constraints
constraints = [
    # Day can only be Monday (1) or Tuesday (2)
    Or(day == 1, day == 2),
    
    # Meeting must be within work hours (9:00 to 17:00)
    nine_am <= start_time,
    start_time + half_hour <= 8 * 60,  # 17:00 in minutes from 9:00
    
    # Margaret's availability
    Not(And(day == 1, 10 * 60 - nine_am <= start_time, start_time < 11 * 60 - nine_am)),  # 10:30 to 11:00
    Not(And(day == 1, 11 * 60 - nine_am <= start_time, start_time < 12 * 60 - nine_am)),  # 11:30 to 12:00
    Not(And(day == 1, 13 * 60 - nine_am <= start_time, start_time < 13 * 60 + 30 - nine_am)),  # 13:00 to 13:30
    Not(And(day == 1, 15 * 60 - nine_am <= start_time, start_time < 17 * 60 - nine_am)),  # 15:00 to 17:00
    Not(And(day == 2, 12 * 60 - nine_am <= start_time, start_time < 12 * 60 + 30 - nine_am)),  # 12:00 to 12:30
    
    # Alexis's availability
    Not(And(day == 1, 9 * 60 + 30 - nine_am <= start_time, start_time < 11 * 60 + 30 - nine_am)),  # 9:30 to 11:30
    Not(And(day == 1, 12 * 60 + 30 - nine_am <= start_time, start_time < 13 * 60 - nine_am)),  # 12:30 to 13:00
    Not(And(day == 1, 14 * 60 - nine_am <= start_time, start_time < 17 * 60 - nine_am)),  # 14:00 to 17:00
    Not(And(day == 2, 9 * 60 - nine_am <= start_time, start_time < 9 * 60 + 30 - nine_am)),  # 9:00 to 9:30
    Not(And(day == 2, 10 * 60 - nine_am <= start_time, start_time < 10 * 60 + 30 - nine_am)),  # 10:00 to 10:30
    Not(And(day == 2, 14 * 60 - nine_am <= start_time, start_time < 16 * 60 + 30 - nine_am)),  # 14:00 to 16:30
    
    # Margaret's preference: no meeting on Monday
    day != 1,
    
    # Margaret's preference: on Tuesday, only after 14:30
    Or(day != 2, start_time >= 14 * 60 + 30 - nine_am)
]

# Create solver instance
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 1 else "Tuesday"
    meeting_start_time_minutes = model[start_time].as_long()
    meeting_start_time = f"{(meeting_start_time_minutes // 60) + 9}:{meeting_start_time_minutes % 60:02}"
    meeting_end_time = f"{((meeting_start_time_minutes + half_hour) // 60) + 9}:{(meeting_start_time_minutes + half_hour) % 60:02}"
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")