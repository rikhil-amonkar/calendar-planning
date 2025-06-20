from z3 import *

def schedule_meeting(adam_schedule, roy_schedule, duration):
    # Define the day of the meeting
    day = 'Monday'

    # Define the start and end times of the work hours
    start_time = 9 * 60
    end_time = 17 * 60

    # Define the variables for the start time of the meeting
    start = Int('start')
    start = If(start < start_time, start, start_time)

    # Define the end time of the meeting
    end = start + duration

    # Define the constraints for Adam's schedule
    adam_constraints = []
    for start, end in adam_schedule:
        adam_constraints.append(And(start <= start, start >= end))
        adam_constraints.append(And(end <= end, end >= start))

    # Define the constraints for Roy's schedule
    roy_constraints = []
    for start, end in roy_schedule:
        roy_constraints.append(And(start <= start, start >= end))
        roy_constraints.append(And(end <= end, end >= start))

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(adam_constraints)
    solver.add(roy_constraints)
    solver.add(start >= start_time)
    solver.add(end <= end_time)
    solver.add(start + duration <= end_time)

    # Check if the solver has a solution
    if solver.check() == sat:
        # Get the model
        model = solver.model()
        # Get the start time from the model
        start_time = model[start].as_long()
        # Calculate the end time
        end_time = start_time + duration
        # Format the start and end times as strings
        start_time_str = '{:02d}:{:02d}'.format(*divmod(start_time, 60))
        end_time_str = '{:02d}:{:02d}'.format(*divmod(end_time, 60))
        # Print the solution
        print('SOLUTION:')
        print(f'Day: {day}')
        print(f'Start Time: {start_time_str}')
        print(f'End Time: {end_time_str}')
    else:
        print('No solution found.')

# Define the schedules for Adam and Roy
adam_schedule = [(9*60 + 30, 10*60), (12*60 + 30, 13*60), (14*60 + 30, 15*60), (16*60 + 30, 17*60)]
roy_schedule = [(10*60, 11*60), (11*60 + 30, 13*60), (13*60 + 30, 14*60 + 30), (16*60 + 30, 17*60)]

# Define the duration of the meeting
duration = 30 * 60

# Schedule the meeting
schedule_meeting(adam_schedule, roy_schedule, duration)