from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = []

# Arthur's schedule
arthur_meetings = {
    0: [(11*60, 11*60+30), (13*60+30, 14*60), (15*60, 15*60+30)],  # Monday
    1: [(13*60, 13*60+30), (16*60, 16*60+30)],  # Tuesday
    2: [(10*60, 10*60+30), (11*60, 11*60+30), (12*60, 12*60+30), (14*60, 14*60+30), (16*60, 16*60+30)]  # Wednesday
}

# Michael's schedule
michael_meetings = {
    0: [(9*60, 12*60), (12*60+30, 13*60), (14*60, 14*60+30), (15*60, 17*60)],  # Monday
    1: [(9*60+30, 11*60+30), (12*60, 13*60+30), (14*60, 15*60+30)],  # Tuesday
    2: [(10*60, 12*60+30), (13*60, 13*60+30)]  # Wednesday
}

# Meeting duration is 30 minutes
meeting_duration = 30

# Constraints for the day
constraints.append(Or(day == 0, day == 2))  # Arthur can't meet on Tuesday

# Constraints for the start time
constraints.append(start_time >= 9*60)  # Start time must be after 9:00
constraints.append(start_time + meeting_duration <= 17*60)  # End time must be before 17:00

# Constraints for Arthur's availability
for d, meetings in arthur_meetings.items():
    for start, end in meetings:
        constraints.append(Or(start_time + meeting_duration <= start, start_time >= end))

# Constraints for Michael's availability
for d, meetings in michael_meetings.items():
    for start, end in meetings:
        constraints.append(Or(start_time + meeting_duration <= start, start_time >= end))

# Solve the constraints
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    meeting_day = ["Monday", "Tuesday", "Wednesday"][model[day].as_long()]
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time//60}:{meeting_start_time%60:02d}\nEnd Time: {meeting_end_time//60}:{meeting_end_time%60:02d}")
else:
    print("No solution found")