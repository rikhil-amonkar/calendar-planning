YOUR_CODE
from z3 import *

# Define the days of the week
days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']

# Define the participants and their schedules
schedules = {
    'Terry': [
        ('Monday', (10, 30), (11, 0)),
        ('Monday', (12, 30), (14, 0)),
        ('Monday', (15, 0), (17, 0)),
        ('Tuesday', (9, 30), (10, 0)),
        ('Tuesday', (10, 30), (11, 0)),
        ('Tuesday', (14, 0), (14, 30)),
        ('Tuesday', (16, 0), (16, 30)),
        ('Wednesday', (9, 30), (10, 30)),
        ('Wednesday', (11, 0), (12, 0)),
        ('Wednesday', (13, 0), (13, 30)),
        ('Wednesday', (15, 0), (16, 0)),
        ('Wednesday', (16, 30), (17, 0)),
        ('Thursday', (9, 30), (10, 0)),
        ('Thursday', (12, 0), (12, 30)),
        ('Thursday', (13, 0), (14, 30)),
        ('Thursday', (16, 0), (16, 30)),
        ('Friday', (9, 0), (11, 30)),
        ('Friday', (12, 0), (12, 30)),
        ('Friday', (13, 30), (16, 0)),
        ('Friday', (16, 30), (17, 0)),
    ],
    'Frances': [
        ('Monday', (9, 30), (11, 0)),
        ('Monday', (11, 30), (13, 0)),
        ('Monday', (14, 0), (14, 30)),
        ('Monday', (15, 0), (16, 0)),
        ('Tuesday', (9, 0), (9, 30)),
        ('Tuesday', (10, 0), (10, 30)),
        ('Tuesday', (11, 0), (12, 0)),
        ('Tuesday', (13, 0), (14, 30)),
        ('Tuesday', (15, 30), (16, 30)),
        ('Wednesday', (9, 30), (10, 0)),
        ('Wednesday', (10, 30), (11, 0)),
        ('Wednesday', (11, 30), (16, 0)),
        ('Wednesday', (16, 30), (17, 0)),
        ('Thursday', (11, 0), (12, 30)),
        ('Thursday', (14, 30), (17, 0)),
        ('Friday', (9, 30), (10, 30)),
        ('Friday', (11, 0), (12, 30)),
        ('Friday', (13, 0), (16, 0)),
        ('Friday', (16, 30), (17, 0)),
    ],
}

# Define the meeting duration
meeting_duration = 30

# Define the solver
solver = Solver()

# Define the variables
day = [Bool(f'day_{i}') for i in range(len(days))]
start_time = [Int(f'start_time_{i}') for i in range(len(days))]
end_time = [Int(f'end_time_{i}') for i in range(len(days))]

# Add constraints for each participant
for participant in ['Terry', 'Frances']:
    for day_name in days:
        day_index = days.index(day_name)
        for schedule in schedules[participant]:
            if schedule[0] == day_name:
                start_time_index = schedule[1][0] * 60 + schedule[1][1]
                end_time_index = schedule[2][0] * 60 + schedule[2][1]
                for i in range(len(days)):
                    if start_time_index < 17 * 60 and start_time_index >= 9 * 60:
                        solver.assert(start_time[i] > start_time_index)
                    if end_time_index < 17 * 60 and end_time_index >= 9 * 60:
                        solver.assert(end_time[i] < end_time_index)

# Add constraints for the meeting duration
for i in range(len(days)):
    solver.assert_and_track(end_time[i] - start_time[i] >= meeting_duration, f'meeting_duration_{i}_constraint')

# Add constraints for Frances' preference to avoid more meetings on Tuesday
solver.assert(day[1] == False)

# Add constraints for the day of the meeting
solver.assert(Or(day[0], day[1], day[2], day[3], day[4]))

# Add constraints for the start and end times
for i in range(len(days)):
    solver.assert(And(9 * 60 <= start_time[i], start_time[i] < 17 * 60))
    solver.assert(And(end_time[i] > 9 * 60, end_time[i] <= 17 * 60))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    day_index = 0
    while model.evaluate(day[day_index]).as_bool().value():
        day_index += 1
    day_name = days[day_index]
    start_time_value = model.evaluate(start_time[day_index]).as_long()
    end_time_value = model.evaluate(end_time[day_index]).as_long()
    print(f'SOLUTION:')
    print(f'Day: {day_name}')
    print(f'Start Time: {str(start_time_value // 60).zfill(2)}:{str(start_time_value % 60).zfill(2)}')
    print(f'End Time: {str(end_time_value // 60).zfill(2)}:{str(end_time_value % 60).zfill(2)}')
else:
    print('No solution found')