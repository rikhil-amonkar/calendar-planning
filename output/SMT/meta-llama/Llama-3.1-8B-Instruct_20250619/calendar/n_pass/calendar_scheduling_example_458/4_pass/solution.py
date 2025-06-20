YOUR_CODE
from z3 import *

def schedule_meeting(day, start_time, end_time, participants, constraints, preferences):
    # Define the variables
    meeting_time = [Bool(f'meeting_time_{i}') for i in range(len(participants))]
    start_times = [Int(f'start_time_{i}') for i in range(len(participants))]
    end_times = [Int(f'end_time_{i}') for i in range(len(participants))]
    
    # Define the constraints
    constraints = []
    for i in range(len(participants)):
        for j in range(len(participants[i])):
            constraints.append(Implies(meeting_time[i], Not(participants[i][j])))
        constraints.append(start_times[i] + 30 <= end_times[i])
        constraints.append(start_times[i] >= 9 * 60)
        constraints.append(end_times[i] <= 17 * 60)
    
    # Add the preference constraint
    for i in range(len(participants)):
        if preferences[i] is not None:
            constraints.append(Implies(meeting_time[i], start_times[i] >= preferences[i]))
    
    # Add the duration constraint
    for i in range(len(participants)):
        constraints.append(start_times[i] + 30 <= end_times[i])
    
    # Solve the constraints
    s = Solver()
    s.add(And(constraints))
    s.add(Or(meeting_time))
    result = s.check()
    
    if result == sat:
        model = s.model()
        for i in range(len(participants)):
            if model.evaluate(meeting_time[i]).as_bool():
                return model.evaluate(start_times[i]).as_int(), model.evaluate(end_times[i]).as_int()
    return None

def find_solution():
    # Define the day
    day = 'Monday'
    
    # Define the participants
    participants = [
        [(0, 60), (150, 180), (180, 210)],  # Melissa
        [(0, 60)],  # Catherine
        [(120, 150), (210, 240)],  # Gregory
        [(0, 30), (210, 240), (270, 300), (330, 360), (390, 420)],  # Victoria
        [(0, 120), (120, 150), (270, 420)],  # Thomas
        [(0, 30), (60, 90), (180, 300), (390, 420), (210, 240), (360, 420)]  # Jennifer
    ]
    
    # Define the preferences
    preferences = [None, None, None, None, None, None]
    for i in range(len(participants)):
        if i == 0:  # Wayne
            preferences[i] = 14 * 60
    
    # Find the solution
    solution = schedule_meeting(day, 0, 24 * 60, participants, participants, preferences)
    
    # Print the solution
    if solution is not None:
        start_time, end_time = solution
        print(f'SOLUTION:')
        print(f'Day: {day}')
        print(f'Start Time: {str(start_time // 60).zfill(2)}:{str(start_time % 60).zfill(2)}')
        print(f'End Time: {str(end_time // 60).zfill(2)}:{str(end_time % 60).zfill(2)}')
    else:
        print('No solution found.')

find_solution()