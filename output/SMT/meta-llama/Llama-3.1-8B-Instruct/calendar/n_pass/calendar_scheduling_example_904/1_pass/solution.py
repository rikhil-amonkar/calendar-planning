from z3 import *

def schedule_meeting(daniel_schedule, bradley_schedule, daniel_preferences, bradley_preferences):
    # Define the days of the week
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    
    # Define the start and end times
    start_time = 9 * 60  # 9:00 in minutes
    end_time = 17 * 60  # 17:00 in minutes
    duration = 30 * 60  # 30 minutes in minutes
    
    # Create a Z3 solver
    s = Solver()
    
    # Declare the variables
    day = [Bool(f'day_{i}') for i in range(len(days))]
    start = [Int(f'start_{i}') for i in range(len(days))]
    end = [Int(f'end_{i}') for i in range(len(days))]
    
    # Add constraints for each day
    for i, d in enumerate(days):
        # Day is not the same as Daniel's or Bradley's preference
        s.add(day[i] == Or(d!= daniel_preferences, d!= bradley_preferences))
        
        # Start and end times are within the work hours
        s.add(And(start[i] >= start_time, start[i] <= end_time - duration))
        
        # End time is 30 minutes after start time
        s.add(end[i] == start[i] + duration)
        
        # Start and end times are not busy for Daniel or Bradley
        s.add(And(Not(Any([start[i] >= d_s and d_s < end[i] for d_s in daniel_schedule[d]])),
                  Not(Any([start[i] >= b_s and b_s < end[i] for b_s in bradley_schedule[d]]))))
        
        # Start time is before end time
        s.add(start[i] < end[i])
    
    # Check if there is a solution
    if s.check() == sat:
        # Get the model
        m = s.model()
        
        # Get the day, start time, and end time
        for i, d in enumerate(days):
            if m.evaluate(day[i]).as_bool():
                day_to_meet = d
                start_time_to_meet = m.evaluate(start[i]).as_int() // 60
                end_time_to_meet = m.evaluate(end[i]).as_int() // 60
                break
        
        # Return the solution
        return f'SOLUTION:\nDay: {day_to_meet}\nStart Time: {start_time_to_meet:02d}:00\nEnd Time: {end_time_to_meet:02d}:00'
    else:
        return 'No solution found'

# Existing schedules for Daniel and Bradley
daniel_schedule = {
    'Monday': [9*60 + 30, 12*60 + 0, 13*60 + 0, 14*60 + 30, 15*60 + 30, 16*60 + 0],
    'Tuesday': [11*60 + 0, 13*60 + 0, 15*60 + 30, 16*60 + 30],
    'Wednesday': [9*60 + 0, 14*60 + 0, 14*60 + 30],
    'Thursday': [10*60 + 30, 12*60 + 0, 14*60 + 30, 15*60 + 30],
    'Friday': [9*60 + 0, 11*60 + 30, 13*60 + 0, 16*60 + 30]
}
bradley_schedule = {
    'Monday': [9*60 + 30, 11*60 + 0, 12*60 + 30, 14*60 + 0],
    'Tuesday': [10*60 + 30, 12*60 + 0, 13*60 + 30, 15*60 + 30],
    'Wednesday': [9*60 + 0, 11*60 + 0, 13*60 + 30, 14*60 + 30, 17*60 + 0],
    'Thursday': [9*60 + 0, 12*60 + 30, 13*60 + 30, 15*60 + 30],
    'Friday': [9*60 + 0, 10*60 + 0, 13*60 + 0, 14*60 + 0, 15*60 + 30]
}

# Preferences
daniel_preferences = 'Wednesday'
bradley_preferences = 'Monday, Tuesday before 12:00, Friday'

print(schedule_meeting(daniel_schedule, bradley_schedule, daniel_preferences, bradley_preferences))