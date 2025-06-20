from z3 import *

def schedule_meeting(anthony_schedules, pamela_schedules, zachary_schedules, max_duration, max_end_time, pamela_preference):
    # Create a new Z3 context
    ctx = Context()

    # Declare the variables
    day = Int('day')
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Define the constraints
    constraints = [
        # Day is Monday
        day == 1,
        # Start time is between 9:00 and 17:00
        And(9 * 60 <= start_time, start_time <= 17 * 60),
        # End time is between 9:00 and 17:00
        And(9 * 60 <= end_time, end_time <= 17 * 60),
        # End time is greater than or equal to start time
        end_time >= start_time,
        # Duration is one hour
        end_time - start_time == max_duration,
        # Anthony is not busy
        Not(Or([start_time >= s[0] and end_time <= s[1] for s in anthony_schedules])),
        # Pamela is not busy
        Not(Or([start_time >= s[0] and end_time <= s[1] for s in pamela_schedules])),
        # Zachary is not busy
        Not(Or([start_time >= s[0] and end_time <= s[1] for s in zachary_schedules])),
        # Pamela does not want to meet after 14:30
        Or([start_time >= 14 * 60 + 30, end_time <= 14 * 60 + 30])
    ]

    # Add the Pamela preference constraint
    constraints.append(start_time >= pamela_preference)

    # Solve the constraints
    solver = Solver(ctx)
    solver.add(constraints)

    # Check if a solution exists
    if solver.check() == sat:
        # Get the solution
        model = solver.model()
        # Extract the solution
        day_value = model[day].as_long()
        start_time_value = model[start_time].as_long()
        end_time_value = model[end_time].as_long()

        # Convert the solution to the required format
        day_str = 'Monday' if day_value == 1 else 'Tuesday' if day_value == 2 else 'Wednesday' if day_value == 3 else 'Thursday' if day_value == 4 else 'Friday' if day_value == 5 else 'Saturday' if day_value == 6 else 'Sunday'
        start_time_str = f'{start_time_value // 60:02d}:{start_time_value % 60:02d}'
        end_time_str = f'{end_time_value // 60:02d}:{end_time_value % 60:02d}'

        # Print the solution
        print(f'SOLUTION:')
        print(f'Day: {day_str}')
        print(f'Start Time: {start_time_str}')
        print(f'End Time: {end_time_str}')
    else:
        print('No solution exists')

# Example usage
anthony_schedules = [(9 * 60 + 30, 10 * 60), (12 * 60, 13 * 60), (16 * 60, 16 * 60 + 30)]
pamela_schedules = [(9 * 60 + 30, 10 * 60), (16 * 60 + 30, 17 * 60)]
zachary_schedules = [(9 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 15 * 60), (16 * 60, 17 * 60)]
max_duration = 60
max_end_time = 17 * 60
pamela_preference = 14 * 60 + 30

schedule_meeting(anthony_schedules, pamela_schedules, zachary_schedules, max_duration, max_end_time, pamela_preference)