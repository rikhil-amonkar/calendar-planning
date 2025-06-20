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
    start_hour = Int('start_hour')
    start_minute = Int('start_minute')
    end_hour = Int('end_hour')
    end_minute = Int('end_minute')
    
    # Add the constraints
    solver.add(day >= 0)
    solver.add(day < 5)
    solver.add(start_hour >= 9)
    solver.add(start_hour < 17)
    solver.add(start_minute >= 0)
    solver.add(start_minute < 60)
    solver.add(end_hour >= 9)
    solver.add(end_hour < 17)
    solver.add(end_minute >= 0)
    solver.add(end_minute < 60)
    solver.add(end_hour * 60 + end_minute - (start_hour * 60 + start_minute) == 30)
    solver.add(start_hour * 60 + start_minute >= 9 * 60)
    solver.add(start_hour * 60 + start_minute <= 16 * 60)
    for day_str, times in eugene_schedules.items():
        for time in times:
            solver.add(If(day == days.index(day_str), start_hour * 60 + start_minute <= time, True))
    for day_str, times in eric_schedules.items():
        for time in times:
            solver.add(If(day == days.index(day_str), start_hour * 60 + start_minute <= time, True))
            solver.add(If(day == days.index(day_str), (end_hour * 60 + end_minute) >= time, True))
    for time in eric_wednesday_preference:
        solver.add(If(day == 2, start_hour * 60 + start_minute + 30 <= time, True))
    solver.add(If(day == 2, start_hour == 11, True))
    
    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        day_str = days[model[day].as_long()]
        start_time_str = str(model[start_hour].as_long()).zfill(2) + ':' + str(model[start_minute].as_long()).zfill(2)
        end_time_str = str(model[end_hour].as_long()).zfill(2) + ':' + str(model[end_minute].as_long()).zfill(2)
        print('SOLUTION:')
        print(f'Day: {day_str}')
        print(f'Start Time: {start_time_str}')
        print(f'End Time: {end_time_str}')
    else:
        print('No solution found')

schedule_meeting()