from z3 import *

def schedule_meeting():
    # Define the day
    day = 'Monday'

    # Define the start and end times
    start_time = 9 * 60  # 9:00
    end_time = 17 * 60  # 17:00

    # Define the meeting duration
    meeting_duration = 30  # half an hour

    # Define the participants and their schedules
    participants = {
        'John': [11 * 60 + 30, 14 * 60, 14 * 60 + 30],
        'Megan': [12 * 60, 14 * 60, 15 * 60, 15 * 60 + 30],
        'Brandon': [],
        'Kimberly': [9 * 60, 10 * 60, 11 * 60, 14 * 60, 15 * 60, 16 * 60, 16 * 60 + 30],
        'Sean': [10 * 60, 11 * 60 + 30, 14 * 60, 15 * 60 + 30],
        'Lori': [9 * 60, 10 * 60 + 30, 13 * 60, 14 * 60, 16 * 60]
    }

    # Define the solver
    s = Solver()

    # Define the variables
    start_time_var = Int('start_time')
    end_time_var = Int('end_time')

    # Add constraints
    s.add(And(start_time <= start_time_var, start_time_var <= end_time))
    s.add(And(start_time_var + meeting_duration <= end_time, end_time_var <= end_time))

    for participant in participants:
        for time in participants[participant]:
            s.add(Or(start_time_var + meeting_duration > time, end_time_var < time))

    # Solve the constraints
    s.check()

    # Get the solution
    solution = s.model()

    # Extract the start and end times from the solution
    start_time_value = solution[start_time_var].as_long()
    end_time_value = solution[end_time_var].as_long()

    # Print the solution
    print(f'SOLUTION:')
    print(f'Day: {day}')
    print(f'Start Time: {start_time_value // 60:02d}:{start_time_value % 60:02d}')
    print(f'End Time: {end_time_value // 60:02d}:{end_time_value % 60:02d}')

schedule_meeting()