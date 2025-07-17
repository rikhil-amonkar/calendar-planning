from z3 import *

# Define the variables for the day and time
day = Int('day')  # 1 for Monday, 2 for Tuesday, 3 for Wednesday
start_hour = Int('start_hour')
start_minute = Int('start_minute')

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the constraints for Nicole's schedule
nicole_busy_times = [
    (1, 9*60, 9*60 + 30),  # Monday 9:00 to 9:30
    (1, 13*60, 13*60 + 30), # Monday 13:00 to 13:30
    (1, 14*60, 15*60),     # Monday 14:30 to 15:30
    (2, 9*60, 9*60 + 30),  # Tuesday 9:00 to 9:30
    (2, 11*60 + 30, 13*60),# Tuesday 11:30 to 13:30
    (2, 14*60, 15*60),     # Tuesday 14:30 to 15:30
    (3, 10*60, 11*60),     # Wednesday 10:00 to 11:00
    (3, 12*60 + 30, 15*60),# Wednesday 12:30 to 15:00
    (3, 16*60, 17*60)      # Wednesday 16:00 to 17:00
]

# Define the constraints for Ruth's schedule
ruth_busy_times = [
    (1, 9*60, 17*60),      # Monday 9:00 to 17:00
    (2, 9*60, 17*60),      # Tuesday 9:00 to 17:00
    (3, 9*60, 10*60 + 30), # Wednesday 9:00 to 10:30
    (3, 11*60, 11*60 + 30),# Wednesday 11:00 to 11:30
    (3, 12*60, 12*60 + 30),# Wednesday 12:00 to 12:30
    (3, 13*60 + 30, 15*60),# Wednesday 13:30 to 15:30
    (3, 16*60, 16*60 + 30) # Wednesday 16:00 to 16:30
]

# Ruth's additional constraint: do not meet after 13:30 on Wednesday
ruth_additional_constraint = Implies(day == 3, start_hour * 60 + start_minute <= 13*60 + 30)

# Create the solver
solver = Solver()

# Add constraints for the day
solver.add(day >= 1)
solver.add(day <= 3)

# Add constraints for the start time
solver.add(start_hour >= 9)
solver.add(start_hour < 17)
solver.add(start_minute >= 0)
solver.add(start_minute < 60)

# Convert start time to minutes since the start of the day
start_time_minutes = start_hour * 60 + start_minute
end_time_minutes = start_time_minutes + meeting_duration

# Add constraints to avoid Nicole's busy times
for d, start, end in nicole_busy_times:
    solver.add(Or(day != d, Or(end_time_minutes <= start, start_time_minutes >= end)))

# Add constraints to avoid Ruth's busy times
for d, start, end in ruth_busy_times:
    solver.add(Or(day != d, Or(end_time_minutes <= start, start_time_minutes >= end)))

# Add Ruth's additional constraint
solver.add(ruth_additional_constraint)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_hour = model[start_hour].as_long()
    meeting_start_minute = model[start_minute].as_long()
    
    # Determine the day name
    day_name = {1: "Monday", 2: "Tuesday", 3: "Wednesday"}[meeting_day]
    
    # Format the start and end times
    start_time_str = f"{meeting_start_hour:02}:{meeting_start_minute:02}"
    end_time_str = f"{(meeting_start_hour + meeting_duration // 60):02}:{(meeting_start_minute + meeting_duration % 60):02}"
    
    # Print the solution
    print("SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")
else:
    print("No solution found")