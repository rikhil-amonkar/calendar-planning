from z3 import *

def schedule_meeting():
    # Define the day of the week (Monday)
    day = 0
    
    # Define the start and end times of the work hours (9:00 to 17:00)
    start_time = 9 * 60
    end_time = 17 * 60
    
    # Define the meeting duration (half an hour)
    meeting_duration = 30
    
    # Define the existing schedules for each participant
    natalie_schedule = [0] * 24 * 60
    david_schedule = [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    douglas_schedule = [1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ralph_schedule = [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    jordan_schedule = [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    
    # Define the preferences for David
    david_preferences = [0] * 24 * 60
    for i in range(14 * 60, end_time):
        david_preferences[i] = 1
    
    # Create a Z3 solver
    s = Solver()
    
    # Define the variables for the start and end times of the meeting
    start_time_var = Int('start_time')
    end_time_var = Int('end_time')
    
    # Define the constraints for the meeting time
    s.add(start_time_var >= start_time)
    s.add(start_time_var + meeting_duration <= end_time)
    s.add(end_time_var <= end_time)
    
    # Define the constraints for the existing schedules
    for i in range(start_time, end_time - meeting_duration + 1):
        s.add(Or(natalie_schedule[i] == 0, natalie_schedule[i + meeting_duration] == 0))
        s.add(Or(david_schedule[i] == 0, david_schedule[i + meeting_duration] == 0))
        s.add(Or(douglas_schedule[i] == 0, douglas_schedule[i + meeting_duration] == 0))
        s.add(Or(ralph_schedule[i] == 0, ralph_schedule[i + meeting_duration] == 0))
        s.add(Or(jordan_schedule[i] == 0, jordan_schedule[i + meeting_duration] == 0))
    
    # Define the constraints for David's preferences
    for i in range(14 * 60, end_time):
        s.add(Implies(david_preferences[i] == 1, Or(start_time_var < i, end_time_var <= i)))
    
    # Solve the constraints
    if s.check() == sat:
        # Get the model
        m = s.model()
        
        # Print the solution
        print('SOLUTION:')
        print(f'Day: {day}')
        print(f'Start Time: {m[start_time_var].as_long() // 60:02d}:{m[start_time_var].as_long() % 60:02d}')
        print(f'End Time: {(m[start_time_var].as_long() // 60 + m[start_time_var].as_long() % 60 + meeting_duration) // 60:02d}:{((m[start_time_var].as_long() // 60 + m[start_time_var].as_long() % 60 + meeting_duration) % 60):02d}')
    else:
        print('No solution found')

schedule_meeting()