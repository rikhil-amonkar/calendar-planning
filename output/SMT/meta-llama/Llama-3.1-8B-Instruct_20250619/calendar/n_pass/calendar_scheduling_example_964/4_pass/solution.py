YOUR_CODE
from z3 import *

def schedule_meeting(betty_schedule, megan_schedule, meeting_duration):
    # Define the days of the week
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    
    # Define the start and end hours of the workday
    start_hour = 9
    end_hour = 17
    
    # Create a solver
    s = Solver()
    
    # Define the variables for the meeting day, start time, and end time
    day = [Bool(f'day_{i}') for i in range(5)]
    start_time = [Int(f'start_time_{i}') for i in range(5)]
    end_time = [Int(f'end_time_{i}') for i in range(5)]
    
    # Add constraints for the meeting day
    s.add(Or([day[0], day[1], day[2], day[3], day[4]]))
    
    # Add constraints for the start and end time
    for i in range(5):
        s.add(start_time[i] >= start_hour)
        s.add(start_time[i] < end_hour)
        s.add(end_time[i] > start_time[i])
        s.add(end_time[i] <= end_hour)
    
    # Add constraints for the meeting duration
    for i in range(5):
        s.add(end_time[i] - start_time[i] == meeting_duration)
    
    # Add constraints for Betty's schedule
    for i in range(5):
        for j in range(start_hour, end_hour):
            s.add(Not(And(day[i], start_time[i] == j, end_time[i] == j + meeting_duration)))
            for k in range(j, j + meeting_duration):
                if j in betty_schedule.get(days[i], []) or j in megan_schedule.get(days[i], []):
                    s.add(Not(And(day[i], start_time[i] == j)))
    
    # Add constraints for Betty's preferences
    s.add(Not(Or([day[2], day[3]])))
    
    # Check if the solver found a solution
    if s.check() == sat:
        # Get the model
        m = s.model()
        
        # Print the solution
        for i in range(5):
            if m.evaluate(day[i]).as_bool():
                print(f'Day: {days[i]}')
                print(f'Start Time: {m.evaluate(start_time[i]).as_int():02d}:00')
                print(f'End Time: {(m.evaluate(start_time[i]).as_int() + meeting_duration):02d}:00')
                print()
    else:
        print('No solution found.')

# Define the existing schedules for Betty and Megan
betty_schedule = {
    'Monday': [10, 11, 16],
    'Tuesday': [9, 10, 12, 13, 16],
    'Wednesday': [13, 14],
    'Thursday': [],
    'Friday': [9, 11, 12, 14]
}

megan_schedule = {
    'Monday': [9, 10, 11, 12, 13, 14, 15, 16],
    'Tuesday': [9, 10, 12, 13, 14, 15, 16],
    'Wednesday': [9, 10, 11, 12, 13, 14, 15, 16, 17],
    'Thursday': [9, 11, 12, 13, 14, 15, 16],
    'Friday': [9, 10, 11, 12, 13, 14, 15, 16, 17]
}

# Define the meeting duration
meeting_duration = 1

schedule_meeting(betty_schedule, megan_schedule, meeting_duration)