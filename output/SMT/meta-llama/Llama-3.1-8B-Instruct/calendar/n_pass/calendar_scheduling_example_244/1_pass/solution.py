from z3 import *

def schedule_meeting():
    # Define the variables
    day = [Bool('day') for _ in range(2)]  # Monday and Tuesday
    start_time = [Int('start_time') for _ in range(2)]
    end_time = [Int('end_time') for _ in range(2)]

    # Define the constraints
    constraints = [
        day[0] == True,  # Meeting is on Monday
        start_time[0] >= 9,  # Start time is after 9:00
        start_time[0] <= 17,  # Start time is before 17:00
        end_time[0] >= 9,  # End time is after 9:00
        end_time[0] <= 17,  # End time is before 17:00
        start_time[0] + 30 <= 17,  # Meeting duration is 30 minutes
        start_time[0] % 30 == 0,  # Start time is a multiple of 30 minutes
    ]

    # Define the participant constraints
    participants = [
        ['Walter', [9, 9, 10, 10, 13, 30, 14, 30, 15, 0, 16, 0]],
        ['Cynthia', [9, 0, 9, 30, 10, 0, 10, 30, 13, 30, 14, 30, 15, 0, 16, 0]],
        ['Ann', [10, 0, 11, 0, 13, 0, 13, 30, 14, 0, 15, 0, 16, 0, 16, 30]],
        ['Catherine', [9, 0, 11, 30, 12, 30, 13, 0, 13, 30, 14, 30, 17, 0]],
        ['Kyle', [9, 0, 9, 30, 10, 0, 11, 30, 12, 0, 12, 30, 13, 0, 14, 30, 15, 0, 16, 0]],
    ]

    for participant, schedule in participants:
        for i in range(1, len(schedule), 2):
            constraints.append(start_time[0] + 30 > schedule[i])
            constraints.append(end_time[0] < schedule[i + 1])

    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    solver.check()
    model = solver.model()

    # Print the solution
    print('SOLUTION:')
    print(f'Day: Monday')
    print(f'Start Time: {model[start_time[0]].as_long():02d}:00')
    print(f'End Time: {(model[start_time[0]].as_long() + 30):02d}:00')

schedule_meeting()