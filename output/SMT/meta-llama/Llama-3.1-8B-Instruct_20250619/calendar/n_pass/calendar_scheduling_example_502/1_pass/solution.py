from z3 import *

def schedule_meeting(jack_schedule, charlotte_schedule, meeting_duration, day, preference=None):
    # Create Z3 variables for the start time
    start_time = Int('start_time')

    # Define the constraints
    constraints = [
        # Ensure the start time is within the work hours
        And(9 * 60 <= start_time, start_time < 17 * 60),
        # Ensure the meeting does not conflict with Jack's schedule
        Or([start_time + meeting_duration > j for j in jack_schedule]),
        # Ensure the meeting does not conflict with Charlotte's schedule
        Or([start_time + meeting_duration > c for c in charlotte_schedule]),
    ]

    # If a preference is given, add it as a constraint
    if preference:
        constraints.append(start_time >= preference)

    # Define the objective function (not used in this case, as we're not optimizing)
    objective = start_time

    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    solver.check()

    # Get the solution
    model = solver.model()
    start_time_value = model[start_time].as_long()

    # Convert the start time to a string
    start_time_str = f'{start_time_value // 60:02d}:{start_time_value % 60:02d}'

    # Calculate the end time
    end_time_str = f'{(start_time_value // 60 + meeting_duration // 60):02d}:{(start_time_value % 60 + meeting_duration % 60):02d}'

    # Print the solution
    print(f'SOLUTION:')
    print(f'Day: {day}')
    print(f'Start Time: {start_time_str}')
    print(f'End Time: {end_time_str}')

# Define the existing schedules for Jack and Charlotte
jack_schedule = [9 * 60 + 30, 10 * 60 + 30, 11 * 60, 11 * 60 + 30, 12 * 60 + 30, 14 * 60, 14 * 60 + 30, 16 * 60]
charlotte_schedule = [9 * 60 + 30, 10 * 60, 10 * 60 + 30, 12 * 60, 12 * 60 + 30, 13 * 60 + 30, 14 * 60, 16 * 60]

# Define the meeting duration
meeting_duration = 30 * 60

# Define the day
day = 'Monday'

# Define the preference (optional)
preference = 12 * 60 + 30

# Schedule the meeting
schedule_meeting(jack_schedule, charlotte_schedule, meeting_duration, day, preference)