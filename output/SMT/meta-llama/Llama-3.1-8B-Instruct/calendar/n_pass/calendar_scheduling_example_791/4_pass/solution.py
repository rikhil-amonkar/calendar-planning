from z3 import *

def schedule_meeting(nicole_schedule, ruth_schedule, meeting_duration, day, ruth_preferences):
    # Define the variables
    start_time = [Int(f'start_time_{i}') for i in range(3)]
    end_time = [Int(f'end_time_{i}') for i in range(3)]

    # Define the constraints
    constraints = []
    for i in range(3):
        constraints.append(And(start_time[i] >= 9, start_time[i] <= 17))
        constraints.append(And(end_time[i] >= 9, end_time[i] <= 17))
        constraints.append(And(start_time[i] + meeting_duration <= 17))
        constraints.append(start_time[i] <= end_time[i])

    # Nicole's constraints
    for i in range(3):
        for j in range(len(nicole_schedule[i])):
            if j == 0:
                constraints.append(Not(And(start_time[i] >= nicole_schedule[i][j], start_time[i] < nicole_schedule[i][j+1])))
            elif j == len(nicole_schedule[i]) - 1:
                constraints.append(Not(And(start_time[i] > nicole_schedule[i][j], start_time[i] <= nicole_schedule[i][j])))
            else:
                constraints.append(Not(And(start_time[i] > nicole_schedule[i][j], start_time[i] < nicole_schedule[i][j+1])))

    # Ruth's constraints
    for i in range(3):
        for j in range(len(ruth_schedule[i])):
            if j == 0:
                constraints.append(Not(And(start_time[i] >= ruth_schedule[i][j], start_time[i] < ruth_schedule[i][j+1])))
            elif j == len(ruth_schedule[i]) - 1:
                constraints.append(Not(And(start_time[i] > ruth_schedule[i][j], start_time[i] <= ruth_schedule[i][j])))
            else:
                constraints.append(Not(And(start_time[i] > ruth_schedule[i][j], start_time[i] < ruth_schedule[i][j+1])))

    # Ruth's preferences
    if day == 'Wednesday':
        constraints.append(Not(And(start_time[2] > 13.5, end_time[2] > 17)))

    # Solve the constraints
    solver = Solver()
    for i in range(3):
        solver.add(constraints[i])
    solver.add(Or([start_time[0] == 9 + j * 30 for j in range(6)]))
    result = solver.check()

    # Print the solution
    if result == sat:
        model = solver.model()
        day = [9 + i * 30 for i in range(6) if model[start_time[0]] == 9 + i * 30][0]
        start_time_value = model[start_time[0]].as_long()
        end_time_value = start_time_value + meeting_duration
        print(f'SOLUTION:')
        print(f'Day: {day}')
        print(f'Start Time: {start_time_value:02d}:00')
        print(f'End Time: {end_time_value:02d}:00')
    else:
        print('No solution found.')

# Define the existing schedules
nicole_schedule = [[9, 9.5, 9.5, 10], [9, 9.5, 11.5, 13.5], [10, 11, 11, 12]]
ruth_schedule = [[9, 17, 17, 17], [9, 17, 17, 17], [9.5, 10.5, 11.5, 11.5, 12, 12.5, 15.5, 16, 16.5]]
meeting_duration = 30
day = 'Tuesday'
ruth_preferences = True

schedule_meeting(nicole_schedule, ruth_schedule, meeting_duration, day, ruth_preferences)