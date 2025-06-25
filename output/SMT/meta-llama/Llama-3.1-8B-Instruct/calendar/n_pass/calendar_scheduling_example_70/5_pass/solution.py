from z3 import *

def schedule_meeting(day, denise_schedule, angela_schedule, natalie_schedule, duration):
    # Create Z3 variables for the start time
    start_time = Int('start_time')
    
    # Create a constraint for the start time to be within the work hours
    constraint1 = And(9 <= start_time, start_time <= 17)
    
    # Create constraints for the end time
    end_time = start_time + duration
    constraint2 = And(end_time <= 17)
    
    # Create constraints for each participant's schedule
    constraint3 = Or([start_time >= ds for ds in denise_schedule])
    constraint4 = start_time >= max(angela_schedule)
    constraint5 = And(start_time >= min(natalie_schedule), start_time + duration <= 17)
    
    # Create a solver and add the constraints
    solver = Solver()
    solver.add([constraint1, constraint2, constraint3, constraint4, constraint5])
    
    # Check if a solution exists
    if solver.check() == sat:
        # Get the model and extract the start time
        model = solver.model()
        start_time_value = model[start_time].as_long()
        
        # Calculate the end time
        end_time_value = start_time_value + duration
        
        # Print the solution
        print(f'SOLUTION:')
        print(f'Day: {day}')
        print(f'Start Time: {start_time_value:02d}:{(start_time_value % 60):02d}')
        print(f'End Time: {end_time_value:02d}:{((end_time_value - duration) % 60):02d}')
    else:
        print('No solution found.')

# Define the existing schedules
denise_schedule = [12*60 + 0, 12*60 + 30, 15*60 + 30, 16*60]
angela_schedule = [9*60, 10*60, 11*60 + 30, 12*60, 13*60, 14*60, 14*60 + 30, 15*60, 17*60]
natalie_schedule = [9*60, 10*60, 11*60 + 30, 12*60, 13*60, 14*60, 14*60 + 30, 15*60, 17*60]

# Define the day and duration
day = 'Monday'
duration = 30

# Call the function
schedule_meeting(day, denise_schedule, angela_schedule, natalie_schedule, duration)