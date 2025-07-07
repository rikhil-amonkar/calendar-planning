from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = [
    # Day must be Monday, Tuesday, or Wednesday
    Or(day == 0, day == 1, day == 2),
    
    # Start time must be within work hours (9:00 to 17:00)
    And(start_time >= 0, start_time <= 480),  # 480 minutes = 8 hours
    
    # Meeting duration is 60 minutes
    start_time + 60 <= 480,
    
    # Patrick's schedule is always free, so no additional constraints for him
    
    # Roy's schedule constraints
    Or(
        # Monday: 9:00-10:00, 11:30-12:00, 13:00-14:00, 14:30-15:00
        Or(start_time + 60 <= 60, start_time >= 75),
        Or(start_time + 60 <= 180, start_time >= 210),
        Or(start_time + 60 <= 240, start_time >= 270),
        Or(start_time + 60 <= 300, start_time >= 330),
        
        # Tuesday: 9:00-10:30, 11:30-12:00, 14:30-15:00, 15:30-16:00
        Or(day != 1, Or(start_time + 60 <= 80, start_time >= 110)),
        Or(day != 1, Or(start_time + 60 <= 180, start_time >= 210)),
        Or(day != 1, Or(start_time + 60 <= 270, start_time >= 300)),
        Or(day != 1, Or(start_time + 60 <= 330, start_time >= 360)),
        
        # Wednesday: 9:30-11:30, 12:30-14:00, 14:30-15:30, 16:30-17:00
        Or(day != 2, Or(start_time + 60 <= 90, start_time >= 180)),
        Or(day != 2, Or(start_time + 60 <= 210, start_time >= 300)),
        Or(day != 2, Or(start_time + 60 <= 330, start_time >= 360)),
        Or(day != 2, Or(start_time + 60 <= 450, start_time >= 480))
    )
]

# Create the solver
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    meeting_day = ["Monday", "Tuesday", "Wednesday"][model[day].as_long()]
    meeting_start_time_minutes = model[start_time].as_long()
    meeting_start_time = f"{9 + meeting_start_time_minutes // 60}:{meeting_start_time_minutes % 60:02}"
    meeting_end_time_minutes = meeting_start_time_minutes + 60
    meeting_end_time = f"{9 + meeting_end_time_minutes // 60}:{meeting_end_time_minutes % 60:02}"
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")