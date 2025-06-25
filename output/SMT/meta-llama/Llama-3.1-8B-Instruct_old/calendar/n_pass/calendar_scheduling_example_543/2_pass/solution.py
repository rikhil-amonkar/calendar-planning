from z3 import *

def schedule_meeting(james_schedule, john_schedule, duration):
    # Create Z3 variables
    day = Int('day')
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Define the domain of the day
    day_domain = [1]  # Assuming we only have one day to consider (Monday)
    
    # Define the domain of the start and end time
    time_domain = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
    
    # Define the constraints for the day
    day_constraints = [day == day_domain[0]]
    
    # Define the constraints for the start and end time
    time_constraints = [And(start_time >= 9, start_time <= 17),
                       And(end_time >= 9, end_time <= 17),
                       start_time < end_time,
                       end_time - start_time == duration]
    
    # Define the constraints for James' schedule
    james_constraints = []
    for i in range(len(james_schedule)):
        james_constraints.append(Or(start_time + i * 30 >= james_schedule[i][0],
                                   start_time + i * 30 + duration <= james_schedule[i][1]))
    
    # Define the constraints for John's schedule
    john_constraints = []
    for i in range(len(john_schedule)):
        john_constraints.append(Or(start_time + i * 30 >= john_schedule[i][0],
                                   start_time + i * 30 + duration <= john_schedule[i][1]))
    
    # Define the constraints for the unavailable time slot on Monday from 12.5 to 13.5
    unavailable_constraints = [And(start_time >= 12.5 * 2, start_time <= 13.5 * 2)]
    
    # Define the solver
    solver = Solver()
    
    # Add the constraints to the solver
    solver.add(day_constraints + time_constraints + james_constraints + john_constraints + unavailable_constraints)
    
    # Check if there is a solution
    if solver.check() == sat:
        # Get the model
        model = solver.model()
        
        # Extract the values from the model
        day_value = model[day].as_long()
        start_time_value = model[start_time].as_long()
        end_time_value = model[end_time].as_long()
        
        # Print the solution
        print(f'SOLUTION:')
        print(f'Day: {day_value}')
        print(f'Start Time: {start_time_value:02d}:00')
        print(f'End Time: {end_time_value:02d}:00')
    else:
        print('No solution found.')

# Example usage
james_schedule = [(11.5, 12.0), (14.5, 15.0)]
john_schedule = [(9.5, 11.0), (11.5, 12.0), (12.5, 13.5), (14.5, 16.5)]
duration = 1

schedule_meeting(james_schedule, john_schedule, duration)