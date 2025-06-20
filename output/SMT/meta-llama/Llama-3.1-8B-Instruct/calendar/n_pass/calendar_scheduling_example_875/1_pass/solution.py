from z3 import *

# Define the days and hours
days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
hours = ['09:00', '09:30', '10:00', '10:30', '11:00', '11:30', '12:00', '12:30', '13:00', '13:30', '14:00', '14:30', '15:00', '15:30', '16:00', '16:30', '17:00']

# Define the meeting duration in hours
meeting_duration = 1

# Define the existing schedules for Natalie and William
natalie_schedule = {
    'Monday': ['09:00-09:30', '10:00-12:00', '12:30-13:00', '14:00-14:30', '15:00-16:30'],
    'Tuesday': ['09:00-09:30', '10:00-10:30', '12:30-14:00', '16:00-17:00'],
    'Wednesday': ['11:00-11:30', '16:00-16:30'],
    'Thursday': ['10:00-11:00', '11:30-15:00', '15:30-16:00', '16:30-17:00']
}

william_schedule = {
    'Monday': ['09:30-11:00', '11:30-17:00'],
    'Tuesday': ['09:00-13:00', '13:30-16:00'],
    'Wednesday': ['09:00-12:30', '13:00-14:30', '15:30-16:00', '16:30-17:00'],
    'Thursday': ['09:00-10:30', '11:00-11:30', '12:00-12:30', '13:00-14:00', '15:00-17:00']
}

# Define the solver
solver = Solver()

# Define the variables
day = [Bool(f'day_{i}') for i in range(4)]
start_hour = [Int(f'start_hour_{i}') for i in range(4)]
end_hour = [Int(f'end_hour_{i}') for i in range(4)]

# Add constraints for the day
for i in range(4):
    solver.add(day[i] == 1)

# Add constraints for the start and end hours
for i in range(4):
    for j in range(len(hours)):
        solver.add(start_hour[i] >= j)
        solver.add(end_hour[i] >= j)
    solver.add(start_hour[i] < end_hour[i])

# Add constraints for the meeting duration
for i in range(4):
    solver.add(end_hour[i] - start_hour[i] >= meeting_duration)

# Add constraints for Natalie's schedule
for day_name, schedule in natalie_schedule.items():
    for time in schedule:
        start, end = time.split('-')
        start_hour_int = int(start[:2]) + (int(start[3:5]) / 60)
        end_hour_int = int(end[:2]) + (int(end[3:5]) / 60)
        for i in range(4):
            if day_name == days[i]:
                solver.add(start_hour[i] > start_hour_int)
                solver.add(start_hour[i] < end_hour_int)
                solver.add(end_hour[i] > start_hour_int)
                solver.add(end_hour[i] < end_hour_int)

# Add constraints for William's schedule
for day_name, schedule in william_schedule.items():
    for time in schedule:
        start, end = time.split('-')
        start_hour_int = int(start[:2]) + (int(start[3:5]) / 60)
        end_hour_int = int(end[:2]) + (int(end[3:5]) / 60)
        for i in range(4):
            if day_name == days[i]:
                solver.add(start_hour[i] > start_hour_int)
                solver.add(start_hour[i] < end_hour_int)
                solver.add(end_hour[i] > start_hour_int)
                solver.add(end_hour[i] < end_hour_int)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    day_index = 0
    for i in range(4):
        if model[day[i]]:
            day_index = i
            break
    start_hour_value = int(model[start_hour[day_index]].as_long())
    end_hour_value = int(model[end_hour[day_index]].as_long())
    start_hour_str = str(start_hour_value // 10) + str(start_hour_value % 10) + ':00'
    end_hour_str = str(end_hour_value // 10) + str(end_hour_value % 10) + ':00'
    print(f'SOLUTION:')
    print(f'Day: {days[day_index]}')
    print(f'Start Time: {start_hour_str}')
    print(f'End Time: {end_hour_str}')
else:
    print('No solution exists')