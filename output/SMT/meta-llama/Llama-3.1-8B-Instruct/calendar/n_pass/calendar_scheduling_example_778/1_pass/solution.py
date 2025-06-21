from z3 import *

# Define the days of the week
days = ['Monday', 'Tuesday', 'Wednesday']

# Define the hours of the day
hours = range(9, 17)

# Define the participants and their schedules
susan_schedule = {
    'Monday': [Time(12, 30), Time(13, 0), Time(13, 30), Time(14, 0)],
    'Tuesday': [Time(11, 30), Time(12, 0)],
    'Wednesday': [Time(9, 30), Time(10, 30), Time(14, 0), Time(14, 30), Time(15, 30), Time(16, 30)]
}

sandra_schedule = {
    'Monday': [Time(9, 0), Time(13, 0), Time(14, 0), Time(15, 0), Time(16, 0), Time(16, 30)],
    'Tuesday': [Time(9, 0), Time(9, 30), Time(10, 30), Time(12, 30), Time(13, 30), Time(14, 0), Time(14, 30), Time(16, 0), Time(17, 0)],
    'Wednesday': [Time(9, 0), Time(11, 30), Time(12, 0), Time(12, 30), Time(13, 0), Time(17, 0)]
}

# Define the meeting duration
meeting_duration = Time(0, 30)

# Define the preferences
susan_preference = 'Tuesday'
sandra_preference = 'Monday'

# Create a Z3 solver
solver = Solver()

# Define the variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints
for day_name in days:
    for start_hour in hours:
        for end_hour in hours:
            if end_hour < start_hour:
                continue
            if day_name == 'Monday':
                susan_block = susan_schedule['Monday']
                sandra_block = sandra_schedule['Monday']
            elif day_name == 'Tuesday':
                susan_block = susan_schedule['Tuesday']
                sandra_block = sandra_schedule['Tuesday']
            else:
                susan_block = susan_schedule['Wednesday']
                sandra_block = sandra_schedule['Wednesday']

            # Check if Susan is free
            susan_free = True
            for block in susan_block:
                if start_time >= block - Time(0, 30) and end_time <= block:
                    susan_free = False
                    break

            # Check if Sandra is free
            sandra_free = True
            for block in sandra_block:
                if start_time >= block - Time(0, 30) and end_time <= block:
                    sandra_free = False
                    break

            # Check if the meeting duration fits
            if susan_free and sandra_free and end_time - start_time == meeting_duration:
                # Check if the day is preferred
                if day_name == susan_preference or day_name == sandra_preference:
                    solver.add(day == day_name)
                    solver.add(start_time == start_hour)
                    solver.add(end_time == end_hour)
                    break
                else:
                    solver.add(day == day_name)
                    solver.add(start_time == start_hour)
                    solver.add(end_time == end_hour)
                    break

# Check if a solution exists
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_string()
    start_time_value = model[start_time].as_string().split(':')[0]
    end_time_value = model[end_time].as_string().split(':')[0]
    print(f'SOLUTION:')
    print(f'Day: {day_value}')
    print(f'Start Time: {start_time_value}:30')
    print(f'End Time: {end_time_value}:30')
else:
    print('No solution exists')