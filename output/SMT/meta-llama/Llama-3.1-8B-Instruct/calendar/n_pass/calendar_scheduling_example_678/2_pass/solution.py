from z3 import *

def schedule_meeting(russell_schedule, alexander_schedule, meeting_duration, day, preference):
    # Create Z3 variables for the meeting start time
    start_time = Int('start_time')
    
    # Create a Z3 solver
    solver = Solver()
    
    # Add constraints for the day
    if day == 'Monday':
        solver.add(And(9 <= start_time, start_time <= 17))
    elif day == 'Tuesday':
        solver.add(And(9 <= start_time, start_time <= 17))
    
    # Add constraints for the meeting duration
    solver.add(And(start_time + meeting_duration <= 17))
    
    # Add constraints for Russell's schedule
    for time in russell_schedule:
        solver.add(Or(start_time + meeting_duration <= time[0], start_time >= time[1]))
    
    # Add constraints for Alexander's schedule
    for time in alexander_schedule:
        solver.add(Or(start_time + meeting_duration <= time[0], start_time >= time[1]))
    
    # Add a constraint for Russell's preference
    if preference:
        solver.add(start_time >= 13.5)
    
    # Check if a solution exists
    if solver.check() == sat:
        # Get the solution
        model = solver.model()
        start_time_value = model[start_time].as_long()
        # Format the start time to HH:MM
        start_time_str = '{:02d}:{:02d}'.format(start_time_value // 60, start_time_value % 60)
        # Calculate the end time
        end_time_value = start_time_value + meeting_duration
        end_time_str = '{:02d}:{:02d}'.format(end_time_value // 60, end_time_value % 60)
        # Print the solution
        print('SOLUTION:')
        print('Day:'+ day)
        print('Start Time:'+ start_time_str)
        print('End Time:'+ end_time_str)
    else:
        # Try to find a solution on Tuesday if no solution is found on Monday
        if day == 'Monday':
            print('No solution found on Monday. Trying Tuesday.')
            schedule_meeting(russell_schedule, alexander_schedule, meeting_duration, 'Tuesday', preference)
        else:
            print('No solution found.')

# Example usage
russell_schedule = [(10.5, 11), (13, 13.5)]
alexander_schedule = [(9, 11.5), (12, 14.5), (15, 17), (9, 10), (13, 14), (15, 15.5), (16, 16.5)]
meeting_duration = 1
day = 'Monday'
preference = True
schedule_meeting(russell_schedule, alexander_schedule, meeting_duration, day, preference)