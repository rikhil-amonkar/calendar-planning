from z3 import *

def schedule_meeting(kayla_schedule, rebecca_schedule, meeting_duration):
    # Define the day of the meeting
    day = 'Monday'

    # Define the start time of the meeting
    start_time = Int('start_time')

    # Define the constraints for the start time
    constraints = [
        And(9 <= start_time, start_time + meeting_duration * 60 <= 17),
        Not(And(start_time >= 10, start_time < 10 + meeting_duration * 60, start_time >= 14.5, start_time < 16)),
        Not(And(start_time >= 9, start_time < meeting_duration * 60, start_time >= 13, start_time < 13.5)),
        Not(And(start_time >= 13.5, start_time < 15, start_time >= 15.5, start_time < 16)),
        Not(And(start_time >= 15.5, start_time < 16, start_time >= 14.5, start_time < 16))
    ]

    # Add the constraints to the solver
    s = Solver()
    s.add(constraints)

    # Check if a solution exists
    if s.check() == sat:
        # Get the solution
        model = s.model()
        start_time_value = model[start_time].as_long()

        # Calculate the end time
        end_time_value = start_time_value + meeting_duration * 60

        # Print the solution
        print(f'SOLUTION:')
        print(f'Day: {day}')
        print(f'Start Time: {start_time_value:02d}:{(start_time_value % 60):02d}')
        print(f'End Time: {end_time_value:02d}:{(end_time_value % 60):02d}')
    else:
        print('No solution exists')

# Test the function
kayla_schedule = [10, 10.5, 14.5, 16]
rebecca_schedule = [9, 13, 13.5, 15, 15.5, 16]
meeting_duration = 1

schedule_meeting(kayla_schedule, rebecca_schedule, meeting_duration)