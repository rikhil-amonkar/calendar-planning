from z3 import *

def schedule_meeting(danielle_schedule, bruce_schedule, eric_schedule, duration):
    # Define the day of the meeting
    day = 'Monday'

    # Define the start time of the meeting
    start_time = Int('start_time')

    # Define the constraints for each person's schedule
    danielle_constraints = []
    for time in danielle_schedule:
        danielle_constraints.append(If(start_time >= time, start_time + duration > time, True))
    danielle_constraints.append(start_time + duration <= 17)  # Ensure the meeting ends before 17:00

    bruce_constraints = []
    for time in bruce_schedule:
        bruce_constraints.append(If(start_time >= time, start_time + duration > time, True))
    bruce_constraints.append(start_time + duration <= 17)  # Ensure the meeting ends before 17:00

    eric_constraints = []
    for time in eric_schedule:
        eric_constraints.append(If(start_time >= time, start_time + duration > time, True))
    eric_constraints.append(start_time + duration <= 17)  # Ensure the meeting ends before 17:00

    # Add the constraints to the solver
    solver = Solver()
    solver.add(danielle_constraints)
    solver.add(bruce_constraints)
    solver.add(eric_constraints)

    # Check if a solution exists
    if solver.check() == sat:
        # Extract the solution
        model = solver.model()
        start_time_value = model[start_time].as_real().numerator / model[start_time].as_real().denominator

        # Print the solution
        print('SOLUTION:')
        print(f'Day: {day}')
        print(f'Start Time: {int(start_time_value):02d}:{int((start_time_value % 1) * 60):02d}')
        print(f'End Time: {int(start_time_value + duration):02d}:{int(((start_time_value + duration) % 1) * 60):02d}')
    else:
        print('No solution exists.')

# Define the existing schedules
danielle_schedule = [9, 10, 10.5, 11, 14.5, 15, 15.5, 16, 16.5, 17]
bruce_schedule = [11, 11.5, 12.5, 13, 14, 14.5, 15.5, 16]
eric_schedule = [9.5, 10, 11, 11.5, 11.5, 13, 14.5, 15.5]

# Define the meeting duration
duration = 1

# Call the function to schedule the meeting
schedule_meeting(danielle_schedule, bruce_schedule, eric_schedule, duration)