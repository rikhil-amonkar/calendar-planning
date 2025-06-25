from z3 import *

# Define the days of the week
days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

# Define the start and end times of the workday
start_time = 9 * 60
end_time = 17 * 60

# Define the duration of the meeting
meeting_duration = 30

# Define the constraints for Ruth's schedule
ruth_schedules = {
    'Monday': (start_time, end_time),
    'Tuesday': (start_time, end_time),
    'Wednesday': (start_time, end_time),
    'Thursday': ((9 * 60, 11 * 60), (11.5 * 60, 14.5 * 60), (15 * 60, end_time))
}

# Define the constraints for Julie's schedule
julie_schedules = {
    'Monday': (start_time, end_time),
    'Tuesday': (start_time, end_time),
    'Wednesday': (start_time, end_time),
    'Thursday': (end_time, end_time)
}

# Define the preferences for Julie
julie_preferences = {
    'Thursday': (11.5 * 60, end_time)
}

# Define the solver
solver = Solver()

# Define the variables
day = Int('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')
end_hour = Int('end_hour')
end_minute = Int('end_minute')

# Add constraints for the day
solver.add(day >= 0)
solver.add(day < len(days))

# Add constraints for the start and end times
solver.add(start_hour >= 9)
solver.add(start_hour <= 17)
solver.add(start_minute >= 0)
solver.add(start_minute <= 59)
solver.add(end_hour >= 9)
solver.add(end_hour <= 17)
solver.add(end_minute >= 0)
solver.add(end_minute <= 59)

# Add constraints for the meeting duration
solver.add((start_hour * 60 + start_minute) + (meeting_duration * 60) <= (end_hour * 60 + end_minute))

# Add constraints for Ruth's schedule
for d, times in ruth_schedules.items():
    if d == days[day]:
        for t in times:
            solver.add((start_hour * 60 + start_minute) >= (t[0] * 60))
            solver.add((start_hour * 60 + start_minute) <= (t[1] * 60))
            solver.add((end_hour * 60 + end_minute) >= (t[0] * 60))
            solver.add((end_hour * 60 + end_minute) <= (t[1] * 60))

# Add constraints for Julie's schedule
for d, times in julie_schedules.items():
    if d == days[day]:
        for t in times:
            solver.add((start_hour * 60 + start_minute) >= (t[0] * 60))
            solver.add((start_hour * 60 + start_minute) <= (t[1] * 60))
            solver.add((end_hour * 60 + end_minute) >= (t[0] * 60))
            solver.add((end_hour * 60 + end_minute) <= (t[1] * 60))

# Add constraints for Julie's preferences
if days[day] == 'Thursday':
    solver.add((start_hour * 60 + start_minute) >= (11.5 * 60))

# Check if a solution exists
if solver.check() == sat:
    model = solver.model()
    day_value = days[model[day].as_long()]
    start_time_value = model[start_hour].as_long() * 60 + model[start_minute].as_long()
    end_time_value = model[end_hour].as_long() * 60 + model[end_minute].as_long()
    print(f"SOLUTION:\nDay: {day_value}\nStart Time: {start_time_value // 60:02d}:{start_time_value % 60:02d}\nEnd Time: {end_time_value // 60:02d}:{end_time_value % 60:02d}")
else:
    print("No solution exists")