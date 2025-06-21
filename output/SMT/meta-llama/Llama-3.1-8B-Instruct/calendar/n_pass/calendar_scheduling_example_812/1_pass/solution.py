from z3 import *

# Define the days of the week
days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

# Define the start and end times of the work hours
start_time = 9 * 60
end_time = 17 * 60

# Define the duration of the meeting
meeting_duration = 30

# Define the existing schedules for Mary and Alexis
mary_schedule = {
    'Monday': [],
    'Tuesday': [(10 * 60, 10 * 60 + 30), (15 * 60, 16 * 60)],
    'Wednesday': [(9 * 60, 10 * 60), (15 * 60, 15 * 60 + 30)],
    'Thursday': [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60)]
}
alexis_schedule = {
    'Monday': [(9 * 60, 10 * 60), (10 * 60 + 30, 12 * 60), (12 * 60 + 30, 16 * 60 + 30)],
    'Tuesday': [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60), (12 * 60, 15 * 60 + 30), (16 * 60, 17 * 60)],
    'Wednesday': [(9 * 60, 11 * 60), (11 * 60 + 30, 17 * 60)],
    'Thursday': [(10 * 60, 12 * 60), (14 * 60, 14 * 60 + 30), (15 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)]
}

# Define the solver
s = Solver()

# Define the variables
day = Int('day')
start_time_var = Int('start_time')
end_time_var = Int('end_time')

# Add the constraints
s.add(day >= 0)
s.add(day < len(days))
s.add(start_time_var >= start_time)
s.add(start_time_var < end_time)
s.add(end_time_var >= start_time_var)
s.add(end_time_var <= end_time)
s.add(end_time_var - start_time_var >= meeting_duration)

# Add the constraints for Mary's schedule
for i, (start, end) in enumerate(mary_schedule[days[day].lower()]):
    s.add(start_time_var >= start)
    s.add(start_time_var < end)
    s.add(end_time_var <= end)

# Add the constraints for Alexis' schedule
for i, (start, end) in enumerate(alexis_schedule[days[day].lower()]):
    s.add(start_time_var >= start)
    s.add(start_time_var < end)
    s.add(end_time_var <= end)

# Check if there is a solution
if s.check() == sat:
    # Get the solution
    model = s.model()
    day_value = days[model[day].as_long()]
    start_time_value = model[start_time_var].as_long()
    end_time_value = model[end_time_var].as_long()

    # Print the solution
    print('SOLUTION:')
    print(f'Day: {day_value}')
    print(f'Start Time: {start_time_value // 60:02d}:{start_time_value % 60:02d}')
    print(f'End Time: {end_time_value // 60:02d}:{end_time_value % 60:02d}')
else:
    print('No solution found')