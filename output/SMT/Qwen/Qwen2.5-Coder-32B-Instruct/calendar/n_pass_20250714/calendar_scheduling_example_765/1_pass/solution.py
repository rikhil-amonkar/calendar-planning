from z3 import *

# Define variables
day = Int('day')  # 1 for Monday, 2 for Tuesday, 3 for Wednesday
start_time = Int('start_time')  # in minutes since 9:00

# Constants for the days
MONDAY = 1
TUESDAY = 2
WEDNESDAY = 3

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Joshua's busy times
joshua_busy_times = {
    MONDAY: [(15*60, 15*60 + 30)],  # 15:00 to 15:30
    TUESDAY: [(11*60 + 30, 12*60), (13*60, 13*60 + 30), (14*60 + 30, 15*60)],  # 11:30 to 12:00, 13:00 to 13:30, 14:30 to 15:00
}

# Joyce's busy times
joyce_busy_times = {
    MONDAY: [(9*60, 9*60 + 30), (10*60, 11*60), (11*60 + 30, 12*60 + 30), (13*60, 15*60), (15*60 + 30, 17*60)],  # 9:00 to 9:30, 10:00 to 11:00, 11:30 to 12:30, 13:00 to 15:00, 15:30 to 17:00
    TUESDAY: [(9*60, 17*60)],  # 9:00 to 17:00
    WEDNESDAY: [(9*60, 9*60 + 30), (10*60, 11*60), (12*60 + 30, 15*60), (16*60, 16*60 + 30)],  # 9:00 to 9:30, 10:00 to 11:00, 12:30 to 15:30, 16:00 to 16:30
}

# Joyce's preference: not before 12:00 on Monday and not Wednesday
joyce_preferences = {
    MONDAY: (12*60, 17*60),
    TUESDAY: (9*60, 17*60),
}

# Create a solver instance
solver = Solver()

# Constraints for the day
solver.add(day >= MONDAY)
solver.add(day <= WEDNESDAY)

# Constraints for the start time
solver.add(start_time >= 0)  # 9:00
solver.add(start_time + meeting_duration <= 8*60)  # 17:00

# Joshua's busy times constraint
for d, times in joshua_busy_times.items():
    for start, end in times:
        solver.add(Or(day != d, Or(start_time + meeting_duration <= start, start_time >= end)))

# Joyce's busy times constraint
for d, times in joyce_busy_times.items():
    for start, end in times:
        solver.add(Or(day != d, Or(start_time + meeting_duration <= start, start_time >= end)))

# Joyce's preference constraint
for d, (pref_start, pref_end) in joyce_preferences.items():
    solver.add(Implies(day == d, And(start_time >= pref_start, start_time + meeting_duration <= pref_end)))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration
    
    # Convert meeting day to string
    if meeting_day == MONDAY:
        meeting_day_str = "Monday"
    elif meeting_day == TUESDAY:
        meeting_day_str = "Tuesday"
    else:
        meeting_day_str = "Wednesday"
    
    # Convert meeting start and end times to HH:MM format
    meeting_start_time_str = f"{9 + meeting_start_time // 60:02}:{meeting_start_time % 60:02}"
    meeting_end_time_str = f"{9 + meeting_end_time // 60:02}:{meeting_end_time % 60:02}"
    
    print(f"SOLUTION:\nDay: {meeting_day_str}\nStart Time: {meeting_start_time_str}\nEnd Time: {meeting_end_time_str}")
else:
    print("No solution found")