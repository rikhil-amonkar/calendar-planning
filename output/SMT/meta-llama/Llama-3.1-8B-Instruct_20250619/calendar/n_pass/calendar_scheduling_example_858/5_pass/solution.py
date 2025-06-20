from z3 import *

def schedule_meeting(carl_schedule, margaret_schedule, meeting_duration, day, avoid_day=None):
    # Create Z3 variables for the start time
    start_time = Int('start_time')
    
    # Create Z3 variables for the end time
    end_time = start_time + meeting_duration
    
    # Define constraints for the start and end times
    constraints = [
        And(9 <= start_time, start_time <= 17),
        And(start_time + meeting_duration <= 17),
        
        # Ensure the meeting is not on a day that Carl wants to avoid
        If(avoid_day == 'Thursday', start_time!= 0, True)
    ]
    
    # Add constraints for each day
    for day_name in ['Monday', 'Tuesday', 'Wednesday', 'Thursday']:
        for start, end in carl_schedule.get(day_name, []):
            constraints.append(Not(And(start <= start_time, end >= start_time)))
        for start, end in margaret_schedule.get(day_name, []):
            constraints.append(Not(And(start <= start_time, end >= start_time)))
    
    # Add constraints for the specific day
    if day == 'Monday':
        constraints.append(Not(And(11 <= start_time, start_time <= 11.5)))
        constraints.append(Or(start_time < 9, start_time > 10.5))
    elif day == 'Tuesday':
        constraints.append(Or(start_time < 9.5, start_time > 12, start_time > 14.5, start_time > 15))
    elif day == 'Wednesday':
        constraints.append(Or(start_time < 9.5, start_time > 12, start_time > 12.5, start_time > 13, start_time > 13.5, start_time > 15))
        constraints.append(Not(And(10 <= start_time, start_time <= 11.5)))
        constraints.append(Not(And(13 <= start_time, start_time <= 13.5)))
    elif day == 'Thursday':
        constraints.append(Or(start_time < 10, start_time > 12, start_time > 12.5, start_time > 14, start_time > 14.5, start_time > 17))
    
    # Create a Z3 solver and add the constraints
    solver = Solver()
    solver.add(constraints)
    
    # Check if there is a solution
    if solver.check() == sat:
        # Get the solution
        model = solver.model()
        start_time_value = model[start_time].as_long()
        day_name = day
        
        # Print the solution
        print(f'SOLUTION:')
        print(f'Day: {day_name}')
        print(f'Start Time: {start_time_value:02d}:00')
        print(f'End Time: {(start_time_value + meeting_duration):02d}:00')
    else:
        print('No solution found.')

# Define the schedules for Carl and Margaret
carl_schedule = {
    'Monday': [(11, 11.5), (14.5, 15)],
    'Tuesday': [(14.5, 15)],
    'Wednesday': [(10, 11.5), (13, 13.5)],
    'Thursday': [(13.5, 14), (16, 16.5)]
}
margaret_schedule = {
    'Monday': [(9, 10.5), (11, 17)],
    'Tuesday': [(9.5, 12), (13.5, 14), (15.5, 17)],
    'Wednesday': [(9.5, 12), (12.5, 13), (13.5, 14.5), (15, 17)],
    'Thursday': [(10, 12), (12.5, 14), (14.5, 17)]
}

# Define the meeting duration
meeting_duration = 1

# Define the day to schedule the meeting
day = 'Wednesday'

# Define the day that Carl wants to avoid
avoid_day = 'Thursday'

# Schedule the meeting
schedule_meeting(carl_schedule, margaret_schedule, meeting_duration, day, avoid_day)