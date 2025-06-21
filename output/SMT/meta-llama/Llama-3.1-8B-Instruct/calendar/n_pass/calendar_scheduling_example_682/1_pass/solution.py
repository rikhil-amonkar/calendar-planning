from z3 import *

def schedule_meeting():
    # Define the variables
    Monday = Bool('Monday')
    Tuesday = Bool('Tuesday')
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Define the constraints
    constraints = [
        And(start_time >= 9, start_time <= 17),
        And(end_time >= 9, end_time <= 17),
        And(start_time < end_time, end_time - start_time >= 30),
        Not(Or(Monday, Tuesday)),  # Nathan can't meet on Monday
        Or(Not(Monday), start_time > 10, start_time > 11, start_time > 13, start_time > 16),  # Nathan's busy times on Monday
        Or(Not(Tuesday), start_time > 9, start_time > 10, start_time > 11, start_time > 13, start_time > 14, start_time > 15, start_time > 16),  # Nathan's busy times on Tuesday
        Or(Not(Monday), start_time > 9, start_time > 10, start_time > 11, start_time > 12, start_time > 13, start_time > 14, start_time > 15),  # Amanda's busy times on Monday
        Or(Not(Tuesday), start_time > 9, start_time > 10, start_time > 11, start_time > 13, start_time > 14, start_time > 15, start_time > 16, start_time > 17),  # Amanda's busy times on Tuesday
        Or(Not(Tuesday), start_time < 11),  # Amanda doesn't want to meet on Tuesday after 11:00
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

        # Extract the values from the model
        day = 'Monday' if model.evaluate(Monday) else 'Tuesday'
        start_time_val = model.evaluate(start_time).as_long()
        end_time_val = model.evaluate(end_time).as_long()

        # Print the solution
        print('SOLUTION:')
        print(f'Day: {day}')
        print(f'Start Time: {start_time_val:02d}:{(start_time_val % 60):02d}')
        print(f'End Time: {end_time_val:02d}:{(end_time_val % 60):02d}')
    else:
        print('No solution found.')

schedule_meeting()