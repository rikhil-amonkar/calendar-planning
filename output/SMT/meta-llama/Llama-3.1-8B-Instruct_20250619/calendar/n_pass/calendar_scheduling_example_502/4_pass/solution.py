from z3 import *

def schedule_meeting(jack_schedule, charlotte_schedule, meeting_duration, day, preference=None):
    # Define the meeting duration in minutes
    meeting_duration_minutes = meeting_duration * 60

    # Create Z3 variables for the start time
    start_time = Int('start_time')

    # Define the constraints
    constraints = [
        # Ensure the start time is within the work hours
        And(9 * 60 <= start_time, start_time < 17 * 60),
        # Ensure the meeting does not conflict with Jack's schedule
        Or([start_time + meeting_duration_minutes < j for j in jack_schedule]),
        # Ensure the meeting does not conflict with Charlotte's schedule
        Or([start_time + meeting_duration_minutes < c for c in charlotte_schedule]),
        # Ensure the meeting duration is exactly 0.5 hours
        start_time + meeting_duration_minutes < 17 * 60,
        start_time + meeting_duration_minutes >= 9 * 60,
        start_time + meeting_duration_minutes >= 9 * 60 + 30,  # Jack's first available time
        start_time + meeting_duration_minutes >= 10 * 60,  # Charlotte's first available time
        # Ensure Jack's constraint after 12:30 is satisfied
        Or([start_time + meeting_duration_minutes < 13 * 60 + 30, start_time + meeting_duration_minutes >= 12 * 60 + 30]),
    ]

    # If a preference is given, add it as a constraint
    if preference:
        constraints.append(start_time >= preference)

    # Define the objective function (not used in this case, as we're not optimizing)
    objective = start_time

    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    result = solver.check()

    # Check if the solution exists
    if result == sat:
        # Get the model
        model = solver.model()
        start_time_value = model[start_time].as_long()

        # Convert the start time to a string
        start_time_str = f'{start_time_value // 60:02d}:{start_time_value % 60:02d}'

        # Calculate the end time
        end_time_str = f'{(start_time_value // 60 + meeting_duration_minutes // 60):02d}:{(start_time_value % 60 + meeting_duration_minutes % 60):02d}'

        # Print the solution
        print(f'SOLUTION:')
        print(f'Day: {day}')
        print(f'Start Time: {start_time_str}')
        print(f'End Time: {end_time_str}')
    elif result == unsat:
        print("No solution exists.")
    else:
        print("Unknown result.")

# Define the existing schedules for Jack and Charlotte
jack_schedule = [9 * 60 + 30, 10 * 60 + 30, 11 * 60, 11 * 60 + 30, 12 * 60 + 30, 14 * 60, 14 * 60 + 30, 16 * 60]
charlotte_schedule = [9 * 60 + 30, 10 * 60, 10 * 60 + 30, 12 * 60, 12 * 60 + 30, 13 * 60 + 30, 14 * 60, 16 * 60]

# Define the meeting duration
meeting_duration = 30

# Define the day
day = 'Monday'

# Define the preference (optional)
preference = 12 * 60 + 30

# Schedule the meeting
schedule_meeting(jack_schedule, charlotte_schedule, meeting_duration, day, preference)