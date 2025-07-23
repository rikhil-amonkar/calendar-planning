from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = [
    # Day constraints
    Or(day == 0, day == 1, day == 2),
    
    # Time constraints (9:00 to 17:00 in minutes)
    start_time >= 0,  # 9:00
    start_time + 60 <= 480,  # 17:00 (480 minutes from 9:00)
    
    # Martha's constraints
    Or(day != 0, Or(start_time >= 120, start_time <= 60)),  # Monday 16:00 to 17:00 (60 to 120 minutes from 9:00)
    Or(day != 1, Or(start_time >= 93, start_time <= 90)),  # Tuesday 15:00 to 15:30 (90 to 93 minutes from 9:00)
    Or(day != 2, Or(start_time >= 360, start_time <= 300)),  # Wednesday 10:00 to 11:00 (300 to 360 minutes from 9:00)
    Or(day != 2, Or(start_time >= 330, start_time <= 320)),  # Wednesday 14:00 to 14:30 (320 to 330 minutes from 9:00)
    
    # Beverly's constraints
    Or(day != 0, Or(start_time >= 300, start_time <= 270)),  # Monday 13:30 to 14:00 (270 to 300 minutes from 9:00)
    Or(day != 0, Or(start_time >= 480, start_time <= 300)),  # Monday 14:00 to 17:00 (300 to 480 minutes from 9:00)
    Or(day != 1, Or(start_time >= 480, start_time <= 0)),  # Tuesday 9:00 to 17:00 (0 to 480 minutes from 9:00)
    Or(day != 2, Or(start_time >= 600, start_time <= 570)),  # Wednesday 9:30 to 10:00 (570 to 600 minutes from 9:00)
    Or(day != 2, Or(start_time >= 1020, start_time <= 990)),  # Wednesday 16:30 to 17:00 (990 to 1020 minutes from 9:00)
    Or(day != 2, Or(start_time >= 450, start_time <= 360)),  # Wednesday 15:30 to 16:30 (360 to 450 minutes from 9:00)
]

# Create a solver
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    print(f"Meeting can be scheduled on day {model[day]} at {model[start_time]} minutes from 9:00.")
else:
    print("No available time for the meeting.")