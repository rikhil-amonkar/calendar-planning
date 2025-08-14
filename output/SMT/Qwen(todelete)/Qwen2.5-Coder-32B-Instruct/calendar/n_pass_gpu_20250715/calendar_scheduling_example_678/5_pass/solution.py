from z3 import *

# Define variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 9:00

# Constants for time conversion
nine_am = 0  # 9:00 in minutes from 9:00
five_pm = 480  # 17:00 in minutes from 9:00
one_hour = 60  # one hour in minutes

# Define constraints
constraints = [
    # Day constraint: either Monday or Tuesday
    Or(day == 0, day == 1),
    
    # Time constraints: meeting must start between 9:00 and 16:00 (inclusive)
    nine_am <= start_time,
    start_time + one_hour <= five_pm,
    
    # Russell's constraints
    Not(And(day == 0, 10*60 + 30 <= start_time, start_time < 11*60)),  # Russell is busy Monday 10:30-11:00
    Not(And(day == 1, 13*60 <= start_time, start_time < 13*60 + 30)),  # Russell is busy Tuesday 13:00-13:30
    
    # Alexander's constraints
    Not(And(day == 0, nine_am <= start_time, start_time < 11*60 + 30)),  # Alexander is busy Monday 9:00-11:30
    Not(And(day == 0, 12*60 <= start_time, start_time < 14*60 + 30)),  # Alexander is busy Monday 12:00-14:30
    Not(And(day == 0, 15*60 <= start_time, start_time < 17*60)),       # Alexander is busy Monday 15:00-17:00
    Not(And(day == 1, nine_am <= start_time, start_time < 10*60)),     # Alexander is busy Tuesday 9:00-10:00
    Not(And(day == 1, 13*60 <= start_time, start_time < 14*60)),       # Alexander is busy Tuesday 13:00-14:00
    Not(And(day == 1, 15*60 <= start_time, start_time < 15*60 + 30)),  # Alexander is busy Tuesday 15:00-15:30
    Not(And(day == 1, 16*60 <= start_time, start_time < 16*60 + 30)),  # Alexander is busy Tuesday 16:00-16:30
    
    # Russell's preference: if possible, do not meet on Tuesday before 13:30
    If(day == 1, start_time >= 13*60, True)  # Russell prefers not to meet before 13:30 on Tuesday
]

# Create solver instance
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time = 9 + model[start_time].as_long() // 60
    meeting_start_minute = model[start_time].as_long() % 60
    meeting_end_time = meeting_start_time + 1
    meeting_end_minute = meeting_start_minute
    
    print(f"SOLUTION:")
    print(f"Day: {meeting_day}")
    print(f"Start Time: {meeting_start_time:02}:{meeting_start_minute:02}")
    print(f"End Time: {meeting_end_time:02}:{meeting_end_minute:02}")
else:
    print("No solution found")