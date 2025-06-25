from z3 import *

def schedule_meeting(participants, meeting_duration, preferences=None):
    # Define the day of the meeting
    day = 'Monday'

    # Define the start time of the meeting
    start_time = Int('start_time')

    # Define the constraints for each participant
    constraints = []
    for participant, schedule in participants.items():
        for time in schedule:
            if len(time) == 2:
                constraints.append(And(start_time >= time[0]*60 + time[1], start_time < (time[0]+1)*60 + time[1]))
            elif len(time) == 4:
                constraints.append(And(start_time >= time[0]*60 + time[1], start_time < (time[0]+1)*60 + time[1]))
                constraints.append(And(start_time >= time[2]*60 + time[3], start_time < (time[2]+1)*60 + time[3]))
            else:
                raise ValueError("Invalid time format")

    # Define the constraint for the meeting duration
    end_time = start_time + meeting_duration

    # Define the constraint for Megan's preference
    if preferences and 'Megan' in preferences and 'avoid_before' in preferences['Megan']:
        constraints.append(And(start_time >= 10*60, end_time < 17*60))

    # Define the solver and add the constraints
    solver = Solver()
    solver.add(constraints)

    # Check if a solution exists
    if solver.check() == sat:
        # Extract the solution
        model = solver.model()
        start_time_value = model[start_time].as_long()

        # Find a valid end time
        end_time_value = start_time_value + meeting_duration.as_long()
        while end_time_value >= 17*60:
            start_time_value += 1
            end_time_value = start_time_value + meeting_duration.as_long()

        # Print the solution
        print(f'DAY: {day}')
        print(f'START TIME: {(start_time_value // 60):02d}:{(start_time_value % 60):02d}')
        print(f'END TIME: {(end_time_value // 60):02d}:{(end_time_value % 60):02d}')
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