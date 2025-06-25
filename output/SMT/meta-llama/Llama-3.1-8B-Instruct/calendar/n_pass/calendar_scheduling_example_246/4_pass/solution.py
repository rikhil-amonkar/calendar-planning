from z3 import *

def schedule_meeting():
    # Define the variables
    day = 'Monday'
    start_time = 9 * 60
    end_time = 17 * 60
    duration = 30
    participants = ['Jacob', 'Diana', 'Adam', 'Angela', 'Dennis']
    busy_times = {
        'Jacob': [(13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60)],
        'Diana': [(9 * 60 + 30, 10 * 60), (11 * 60 + 30, 12 * 60), (13 * 60, 13 * 60 + 30), (16 * 60, 16 * 60 + 30)],
        'Adam': [(9 * 60 + 30, 10 * 60 + 30), (11 * 60, 12 * 60 + 30), (15 * 60 + 30, 16 * 60)],
        'Angela': [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 12 * 60), (13 * 60, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)],
        'Dennis': [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 11 * 60 + 30), (13 * 60, 15 * 60), (16 * 60 + 30, 17 * 60)]
    }

    # Create the solver
    s = Solver()

    # Define the variables for the start time
    start = Int('start')

    # Define the constraints
    for participant in participants:
        for start_time_participant, end_time_participant in busy_times[participant]:
            s.add(start + duration > start_time_participant * 60)
            s.add(start + duration <= end_time_participant * 60)

    # Add the constraints for the day and duration
    s.add(start >= 9 * 60)
    s.add(start + duration <= 17 * 60)

    # Check if a solution exists
    if s.check() == sat:
        # Get the model
        m = s.model()

        # Print the solution
        print('SOLUTION:')
        print(f'Day: {day}')
        print(f'Start Time: {m[start] // 60:02d}:{m[start] % 60:02d}')
        print(f'End Time: {(m[start] // 60 + duration // 60) % 24:02d}:{(m[start] % 60 + duration % 60) % 60:02d}')
    else:
        print('No solution exists.')

schedule_meeting()