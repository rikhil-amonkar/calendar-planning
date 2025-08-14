from z3 import *

# Define the variables for the day and time
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday
start_hour = Int('start_hour')
start_minute = Int('start_minute')

# Define the constraints for the meeting duration
meeting_duration = 60  # 1 hour

# Define the constraints for the work hours
work_start = 9
work_end = 17

# Define the constraints for each participant's busy times
natalie_busy_times = {
    0: [(9, 9.5), (10, 12), (12.5, 13), (14, 14.5), (15, 16.5)],  # Monday
    1: [(9, 9.5), (10, 10.5), (12.5, 14), (16, 17)],              # Tuesday
    2: [(11, 11.5), (16, 16.5)],                                 # Wednesday
    3: [(10, 11), (11.5, 15), (15.5, 16), (16.5, 17)]             # Thursday
}

william_busy_times = {
    0: [(9.5, 11), (11.5, 17)],                                  # Monday
    1: [(9, 13), (13.5, 16)],                                    # Tuesday
    2: [(9, 12.5), (13, 14.5), (15.5, 16), (16.5, 17)],            # Wednesday
    3: [(9, 10.5), (11, 11.5), (12, 12.5), (13, 14), (15, 17)]     # Thursday
}

# Create the solver
solver = Solver()

# Add constraints for the day
solver.add(day >= 0)
solver.add(day <= 3)

# Add constraints for the start time within work hours
solver.add(start_hour >= work_start)
solver.add(start_hour < work_end)
solver.add(start_minute >= 0)
solver.add(start_minute < 60)

# Convert start time to total minutes from 9:00
start_time_minutes = (start_hour - work_start) * 60 + start_minute

# Add constraints to avoid busy times for Natalie
for d, busy_times in natalie_busy_times.items():
    for start, end in busy_times:
        start_minutes = (start - work_start) * 60
        end_minutes = (end - work_start) * 60
        solver.add(Or(start_time_minutes + meeting_duration <= start_minutes, start_time_minutes >= end_minutes))

# Add constraints to avoid busy times for William
for d, busy_times in william_busy_times.items():
    for start, end in busy_times:
        start_minutes = (start - work_start) * 60
        end_minutes = (end - work_start) * 60
        solver.add(Or(start_time_minutes + meeting_duration <= start_minutes, start_time_minutes >= end_minutes))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_hour_value = model[start_hour].as_long()
    start_minute_value = model[start_minute].as_long()
    
    # Convert day number to name
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    day_name = days[day_value]
    
    # Format start and end times
    start_time_str = f"{start_hour_value:02}:{start_minute_value:02}"
    end_time_str = f"{(start_hour_value + (start_minute_value + meeting_duration) // 60):02}:{(start_minute_value + meeting_duration) % 60:02}"
    
    print(f"SOLUTION:\nDay: {day_name}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")