from z3 import *

# Define the variables for the day and time
day = Int('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')

# Define the duration of the meeting
meeting_duration = 30

# Define the possible days and their corresponding integer values
days = {'Monday': 1, 'Tuesday': 2, 'Wednesday': 3}

# Define the constraints
constraints = []

# Joshua's availability
constraints.append(Or(day != days['Monday'], Or(start_hour * 60 + start_minute < 15 * 60, start_hour * 60 + start_minute >= 15 * 60 + 30)))
constraints.append(Or(day != days['Tuesday'], Or(start_hour * 60 + start_minute < 11 * 60 + 30, start_hour * 60 + start_minute >= 12 * 60)))
constraints.append(Or(day != days['Tuesday'], Or(start_hour * 60 + start_minute < 13 * 60, start_hour * 60 + start_minute >= 13 * 60 + 30)))
constraints.append(Or(day != days['Tuesday'], Or(start_hour * 60 + start_minute < 14 * 60 + 30, start_hour * 60 + start_minute >= 15 * 60)))

# Joyce's availability
constraints.append(Or(day != days['Monday'], Or(start_hour * 60 + start_minute < 9 * 60 + 30, start_hour * 60 + start_minute >= 12 * 60)))
constraints.append(Or(day != days['Monday'], Or(start_hour * 60 + start_minute < 13 * 60, start_hour * 60 + start_minute >= 15 * 60 + 30)))
constraints.append(day != days['Tuesday'])
constraints.append(Or(day != days['Wednesday'], Or(start_hour * 60 + start_minute < 9 * 60 + 30, start_hour * 60 + start_minute >= 11 * 60)))
constraints.append(Or(day != days['Wednesday'], Or(start_hour * 60 + start_minute < 12 * 60 + 30, start_hour * 60 + start_minute >= 15 * 60)))
constraints.append(Or(day != days['Wednesday'], Or(start_hour * 60 + start_minute < 16 * 60, start_hour * 60 + start_minute >= 16 * 60 + 30)))

# Joyce's preference: not before 12:00 on Monday
constraints.append(Or(day != days['Monday'], start_hour * 60 + start_minute >= 12 * 60))

# Meeting must be within work hours (9:00 to 17:00)
constraints.append(start_hour * 60 + start_minute >= 9 * 60)
constraints.append(start_hour * 60 + start_minute + meeting_duration <= 17 * 60)

# Day must be one of the specified days
constraints.append(day >= min(days.values()))
constraints.append(day <= max(days.values()))

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = [k for k, v in days.items() if v == model[day].as_long()][0]
    meeting_start_time = f"{model[start_hour].as_long():02}:{model[start_minute].as_long():02}"
    meeting_end_time = f"{(model[start_hour].as_long() + (model[start_minute].as_long() + meeting_duration) // 60):02}:{((model[start_minute].as_long() + meeting_duration) % 60):02}"
    
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")