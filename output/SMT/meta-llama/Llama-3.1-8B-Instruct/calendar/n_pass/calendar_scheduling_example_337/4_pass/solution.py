from z3 import *

def schedule_meeting():
    # Define the variables
    day = 'Monday'
    start_time = Int('start_time')
    end_time = Int('end_time')
    meeting_duration = 30  # in minutes

    # Define the constraints
    constraints = [
        # John's constraints
        start_time > 11,
        start_time < 12,
        start_time > 14,
        start_time < 14.5,
        # Megan's constraints
        start_time > 12,
        start_time < 12.5,
        start_time > 14.5,
        start_time < 15,
        start_time > 15.5,
        start_time < 16,
        # Brandon's constraints
        start_time >= 9,
        start_time <= 17 - meeting_duration,
        # Kimberly's constraints
        start_time > 9,
        start_time < 9.5,
        start_time > 10,
        start_time < 10.5,
        start_time > 11,
        start_time < 11.5,
        start_time > 14.5,
        start_time < 15,
        start_time > 15.5,
        start_time < 16,
        start_time > 16.5,
        start_time < 17,
        # Sean's constraints
        start_time > 10,
        start_time < 11,
        start_time > 11.5,
        start_time < 14,
        start_time > 14.5,
        start_time < 15,
        start_time > 15.5,
        start_time < 16,
        # Lori's constraints
        start_time > 9,
        start_time < 9.5,
        start_time > 10.5,
        start_time < 12,
        start_time > 13,
        start_time < 14.5,
        start_time > 16,
        start_time < 16.5,
        # Meeting duration constraint
        start_time >= 9,
        start_time <= 17 - meeting_duration,
        # Ensure end time is greater than start time
        end_time > start_time,
        # Calculate end time based on start time and meeting duration
        end_time == start_time + meeting_duration,
    ]

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    for constraint in constraints:
        solver.add(constraint)

    # Check if a solution exists
    if solver.check() == sat:
        # Get the model
        model = solver.model()

        # Extract the start and end times
        start_time_value = model[start_time].as_real().numerator() / model[start_time].as_real().denominator()
        end_time_value = model[end_time].as_real().numerator() / model[end_time].as_real().denominator()

        # Print the solution
        print(f'SOLUTION:')
        print(f'Day: {day}')
        print(f'Start Time: {int(start_time_value // 1):02d}:{int((start_time_value % 1) * 60 // 1):02d}')
        print(f'End Time: {int(end_time_value // 1):02d}:{int((end_time_value % 1) * 60 // 1):02d}')
    else:
        print('No solution exists')

schedule_meeting()