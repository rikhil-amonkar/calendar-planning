from z3 import *

def schedule_meeting(lisa_schedule, anthony_schedule, meeting_duration):
    # Create Z3 variables for the day, start time, and end time
    day = Bool('day')
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Define the constraints for the day
    constraints = [day == True]  # We only consider Monday

    # Define the constraints for the start and end times
    constraints.append(And(start_time >= 9, start_time <= 17))  # Between 9:00 and 17:00
    constraints.append(And(end_time >= 9, end_time <= 17))  # Between 9:00 and 17:00
    constraints.append(start_time < end_time)  # Start time must be before end time
    constraints.append(end_time - start_time == meeting_duration)  # Meeting duration

    # Define the constraints for Lisa's schedule
    lisa_constraints = []
    for start, end in lisa_schedule:
        lisa_constraints.append(Or(And(start_time >= start, start_time < end),
                                   And(end_time > start, end_time <= end)))
    constraints.extend(lisa_constraints)

    # Define the constraints for Anthony's schedule
    anthony_constraints = []
    for start, end in anthony_schedule:
        anthony_constraints.append(Or(And(start_time >= start, start_time < end),
                                       And(end_time > start, end_time <= end)))
    constraints.extend(anthony_constraints)

    # Define the constraints for the meeting time
    constraints.append(And(start_time >= 9, start_time < 17))  # Between 9:00 and 16:59
    constraints.append(And(end_time > 9, end_time <= 17))  # Between 10:00 and 17:00

    # Create a Z3 solver and add the constraints
    solver = Solver()
    solver.add(constraints)

    # Check if there is a solution
    if solver.check() == sat:
        # Get the model
        model = solver.model()
        # Extract the values from the model
        day_val = model.evaluate(day).as_bool()
        start_time_val = model.evaluate(start_time).as_long()
        end_time_val = model.evaluate(end_time).as_long()
        # Print the solution
        print(f'SOLUTION:')
        print(f'Day: {["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"][int(day_val)]}')
        print(f'Start Time: {start_time_val:02d}:{(start_time_val % 100):02d}')
        print(f'End Time: {end_time_val:02d}:{(end_time_val % 100):02d}')
    else:
        print('No solution found.')

# Example usage
lisa_schedule = [(9, 9.5), (10.5, 11), (14, 16)]
anthony_schedule = [(9, 9.5), (11, 11.5), (12.5, 13.5), (14, 15), (15.5, 16), (16.5, 17)]
meeting_duration = 30

schedule_meeting(lisa_schedule, anthony_schedule, meeting_duration)