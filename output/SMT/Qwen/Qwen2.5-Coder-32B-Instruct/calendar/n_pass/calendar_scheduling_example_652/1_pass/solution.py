from z3 import *

# Define the variables for the day and time
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 00:00

# Constants for the meeting duration and work hours
meeting_duration = 30  # in minutes
work_start = 9 * 60  # 09:00 in minutes
work_end = 17 * 60  # 17:00 in minutes

# Constraints for Jesse's availability
jesse_busy_monday = [(13*60 + 30, 14*60), (14*60 + 30, 15*60)]
jesse_busy_tuesday = [(9*60, 9*60 + 30), (13*60, 13*60 + 30), (14*60, 15*60)]

# Constraints for Lawrence's availability
lawrence_busy_monday = [(9*60, 17*60)]
lawrence_busy_tuesday = [(9*60 + 30, 10*60 + 30), (11*60 + 30, 12*60 + 30),
                         (13*60, 13*60 + 30), (14*60 + 30, 15*60),
                         (15*60 + 30, 16*60 + 30)]

# Create the solver
solver = Solver()

# Add constraints for the day
solver.add(Or(day == 0, day == 1))

# Add constraints for the start time
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Add constraints for Jesse's availability
for busy_start, busy_end in jesse_busy_monday:
    solver.add(Or(day != 0, Or(start_time + meeting_duration <= busy_start, start_time >= busy_end)))

for busy_start, busy_end in jesse_busy_tuesday:
    solver.add(Or(day != 1, Or(start_time + meeting_duration <= busy_start, start_time >= busy_end)))

# Add constraints for Lawrence's availability
for busy_start, busy_end in lawrence_busy_monday:
    solver.add(Or(day != 0, Or(start_time + meeting_duration <= busy_start, start_time >= busy_end)))

for busy_start, busy_end in lawrence_busy_tuesday:
    solver.add(Or(day != 1, Or(start_time + meeting_duration <= busy_start, start_time >= busy_end)))

# Lawrence can not meet on Tuesday after 16:30
solver.add(Or(day != 1, start_time + meeting_duration <= 16*60 + 30))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration
    
    print(f"SOLUTION:")
    print(f"Day: {meeting_day}")
    print(f"Start Time: {meeting_start_time // 60:02}:{meeting_start_time % 60:02}")
    print(f"End Time: {meeting_end_time // 60:02}:{meeting_end_time % 60:02}")
else:
    print("No solution found")