YOUR_CODE
from z3 import *

# Define the variables
days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
times = ['09:00', '09:30', '10:00', '10:30', '11:00', '11:30', '12:00', '12:30', '13:00', '13:30', '14:00', '14:30', '15:00', '15:30', '16:00', '16:30', '17:00']
meeting_duration = 30

# Convert time strings to minutes
time_in_minutes = {}
for time in times:
    hours, minutes = map(int, time.split(':'))
    time_in_minutes[time] = hours * 60 + minutes

# Define the schedules
mary_schedule = {
    'Monday': [time_in_minutes['09:00'], time_in_minutes['10:00']],
    'Tuesday': [time_in_minutes['10:00'], time_in_minutes['10:30'], time_in_minutes['15:30'], time_in_minutes['16:00']],
    'Wednesday': [time_in_minutes['09:30'], time_in_minutes['10:00'], time_in_minutes['15:00'], time_in_minutes['15:30']],
    'Thursday': [time_in_minutes['09:00'], time_in_minutes['10:00'], time_in_minutes['10:30'], time_in_minutes['11:30']]
}

alexis_schedule = {
    'Monday': [time_in_minutes['09:00'], time_in_minutes['10:00'], time_in_minutes['10:30'], time_in_minutes['12:00'], time_in_minutes['12:30'], time_in_minutes['16:30']],
    'Tuesday': [time_in_minutes['09:00'], time_in_minutes['10:00'], time_in_minutes['10:30'], time_in_minutes['11:30'], time_in_minutes['12:00'], time_in_minutes['15:30'], time_in_minutes['16:00'], time_in_minutes['17:00']],
    'Wednesday': [time_in_minutes['09:00'], time_in_minutes['11:00'], time_in_minutes['11:30'], time_in_minutes['17:00']],
    'Thursday': [time_in_minutes['10:00'], time_in_minutes['12:00'], time_in_minutes['14:00'], time_in_minutes['14:30'], time_in_minutes['15:30'], time_in_minutes['16:00'], time_in_minutes['16:30'], time_in_minutes['17:00']]
}

# Define the solver
solver = Solver()

# Define the variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Add constraints
for d in days:
    for t in times:
        if t in mary_schedule[d] or t in alexis_schedule[d]:
            solver.assert(Not(And(day == d, start_time == time_in_minutes[t], end_time == time_in_minutes[t])))

# Meeting duration constraint
solver.assert(And(start_time < end_time, end_time - start_time == meeting_duration))

# Earliest availability constraint
solver.assert(Or(day == 'Monday', And(day == 'Tuesday', start_time >= time_in_minutes['10:30']), And(day == 'Wednesday', start_time >= time_in_minutes['09:30']), And(day == 'Thursday', start_time >= time_in_minutes['10:30'])))

# Check if a solution exists
if solver.check() == sat:
    # Get the solution
    model = solver.model()
    day_value = days[model[day].as_long()]
    start_time_value = model[start_time].as_long()
    end_time_value = model[end_time].as_long()

    # Convert time from minutes to string
    start_time_str = '{:02d}:{:02d}'.format(*divmod(start_time_value, 60))
    end_time_str = '{:02d}:{:02d}'.format(*divmod(end_time_value, 60))

    # Print the solution
    print('SOLUTION:')
    print(f'Day: {day_value}')
    print(f'Start Time: {start_time_str}')
    print(f'End Time: {end_time_str}')
else:
    print('No solution exists.')