from z3 import *

def schedule_meeting(participants, meeting_duration, preferences=None):
    # Define the day of the meeting
    day = 'Monday'

    # Define the start and end times of the meeting
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Define the constraints for each participant
    constraints = []
    for participant, schedule in participants.items():
        for time in schedule:
            constraints.append(And(start_time >= time[0], start_time < time[1]))
            constraints.append(And(end_time > time[0], end_time >= time[1]))

    # Define the constraint for the meeting duration
    constraints.append(And(start_time + meeting_duration >= end_time))

    # Define the constraint for Megan's preference
    if preferences and 'Megan' in preferences and 'avoid_before' in preferences['Megan']:
        constraints.append(And(start_time >= 10, end_time < 17))

    # Define the solver and add the constraints
    solver = Solver()
    solver.add(constraints)

    # Check if a solution exists
    if solver.check() == sat:
        # Extract the solution
        model = solver.model()
        start_time_value = model[start_time].as_long()
        end_time_value = model[end_time].as_long()

        # Print the solution
        print(f'DAY: {day}')
        print(f'START TIME: {start_time_value:02d}:00')
        print(f'END TIME: {(start_time_value + meeting_duration.as_long()):02d}:00')
    else:
        print('No solution found.')

# Define the participants and their schedules
participants = {
    'Kimberly': [(10, 10, 30), (11, 12, 0), (16, 16, 30)],
    'Megan': [],
    'Marie': [(10, 11, 0), (11, 30, 15, 0), (16, 16, 30)],
    'Diana': [(9, 30, 10, 0), (10, 30, 14, 30), (15, 30, 17, 0)]
}

# Define the meeting duration and preferences
meeting_duration = 30
preferences = {
    'Megan': {'avoid_before': '10:00'}
}

# Schedule the meeting
schedule_meeting(participants, meeting_duration, preferences)