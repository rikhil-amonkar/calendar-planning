from z3 import *

def schedule_meeting(day, start_time, end_time, schedules, preferences=None):
    # Create Z3 solver
    s = Solver()

    # Define variables for each participant's availability
    participants = ['Kimberly', 'Megan', 'Marie', 'Diana']
    variables = {}
    for participant in participants:
        variables[participant] = [Bool(participant + '_' + str(i)) for i in range(len(schedules[participant]))]

    # Add constraints for each participant's schedule
    for participant in participants:
        for i in range(len(schedules[participant])):
            s.add(Implies(variables[participant][i], schedules[participant][i][0] <= start_time))
            s.add(Implies(variables[participant][i], end_time <= schedules[participant][i][1]))

    # Add constraint for Megan's preference
    if preferences and preferences['Megan'] == 'avoid_before_10:00':
        s.add(Implies(variables['Megan'][0], start_time >= 10))

    # Add constraint for meeting duration
    s.add(start_time + 0.5 <= end_time)

    # Add constraint for meeting time
    s.add(9 <= start_time)
    s.add(start_time + 0.5 <= 17)

    # Solve the problem
    s.check()

    # Get the solution
    model = s.model()

    # Print the solution
    print('SOLUTION:')
    print(f'Day: {day}')
    print(f'Start Time: {model[start_time].as_long():02d}:{model[start_time].as_long() % 100:02d}')
    print(f'End Time: {model[end_time].as_long():02d}:{model[end_time].as_long() % 100:02d}')

# Define the schedules for each participant
schedules = {
    'Kimberly': [[10, 10.5], [11, 12], [16, 16.5]],
    'Megan': [],
    'Marie': [[10, 11], [11.5, 15], [16, 16.5]],
    'Diana': [[9.5, 10], [10.5, 14.5], [15.5, 17]]
}

# Define the preferences for each participant
preferences = {
    'Megan': 'avoid_before_10:00'
}

# Schedule the meeting
schedule_meeting('Monday', 0, 0.5, schedules, preferences)