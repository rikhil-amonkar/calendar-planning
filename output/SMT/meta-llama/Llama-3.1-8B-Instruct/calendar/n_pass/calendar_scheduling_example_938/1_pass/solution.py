from z3 import *

def schedule_meeting():
    # Define the days of the week
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    
    # Define the start and end times
    start_time = 9 * 60
    end_time = 17 * 60
    
    # Define the meeting duration
    meeting_duration = 30
    
    # Define the existing schedules for Eugene and Eric
    eugene_schedules = {
        'Monday': [11 * 60, 12 * 60, 13 * 60 + 30, 14 * 60, 16 * 60],
        'Tuesday': [],
        'Wednesday': [9 * 60, 11 * 60, 12 * 60, 13 * 60 + 30, 14 * 60 + 30],
        'Thursday': [9 * 60 + 30, 11 * 60, 12 * 60 + 30],
        'Friday': [10 * 60 + 30, 12 * 60, 13 * 60]
    }
    
    eric_schedules = {
        'Monday': [9 * 60, 17 * 60],
        'Tuesday': [9 * 60, 17 * 60],
        'Wednesday': [9 * 60, 11 * 60, 12 * 60, 14 * 60 + 30, 16 * 60 + 30],
        'Thursday': [9 * 60, 17 * 60],
        'Friday': [9 * 60, 11 * 60, 11 * 60 + 30, 17 * 60]
    }
    
    # Define the preference to avoid Wednesday
    eric_wednesday_preference = [11 * 60, 12 * 60]
    
    # Create a Z3 solver
    solver = Solver()
    
    # Declare the variables
    day = Int('day')
    start_time_var = Int('start_time')
    end_time_var = Int('end_time')
    
    # Add the constraints
    solver.add(day >= 0)
    solver.add(day < 5)
    solver.add(start_time_var >= start_time)
    solver.add(start_time_var < end_time)
    solver.add(end_time_var > start_time_var)
    solver.add(end_time_var <= end_time)
    for day_str, times in eugene_schedules.items():
        for time in times:
            solver.add(If(day == days.index(day_str), start_time_var + meeting_duration <= time, True))
    for day_str, times in eric_schedules.items():
        for time in times:
            solver.add(If(day == days.index(day_str), start_time_var <= time, True))
            solver.add(If(day == days.index(day_str), end_time_var >= time, True))
    for time in eric_wednesday_preference:
        solver.add(If(day == 2, start_time_var + meeting_duration <= time, True))
    
    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        day_str = days[model[day].as_long()]
        start_time_str = str(model[start_time_var].as_long() // 60).zfill(2) + ':' + str(model[start_time_var].as_long() % 60).zfill(2)
        end_time_str = str((model[end_time_var].as_long() // 60) % 24).zfill(2) + ':' + str((model[end_time_var].as_long() % 60) % 60).zfill(2)
        print('SOLUTION:')
        print(f'Day: {day_str}')
        print(f'Start Time: {start_time_str}')
        print(f'End Time: {end_time_str}')
    else:
        print('No solution found')

schedule_meeting()