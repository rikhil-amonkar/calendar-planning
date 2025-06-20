from z3 import *

def schedule_meeting(ronald_schedule, amber_schedule, meeting_duration):
    # Define the days of the week
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Define the start and end times of the workday
    start_time = 9 * 60  # 9:00 in minutes
    end_time = 17 * 60  # 17:00 in minutes
    
    # Create a Z3 solver
    s = Solver()
    
    # Define the variables
    day = [Bool(f'day_{i}') for i in range(len(days))]
    start = [Int(f'start_{i}') for i in range(len(days))]
    end = [Int(f'end_{i}') for i in range(len(days))]
    
    # Add constraints for the days
    for i, d in enumerate(days):
        s.add(Or(day[i], Not(day[i])))
    
    # Add constraints for the start and end times
    for i in range(len(days)):
        s.add(start[i] >= start_time)
        s.add(start[i] < end_time)
        s.add(end[i] > start[i])
        s.add(end[i] <= end_time)
    
    # Add constraints for the meeting duration
    for i in range(len(days)):
        s.add(end[i] - start[i] >= meeting_duration)
    
    # Add constraints for Ronald's schedule
    for i in range(len(days)):
        for j in ronald_schedule.get(days[i], []):
            s.add(Or(start[i] + j[0] > end[i] + j[1], start[i] + j[0] < start[i], end[i] + j[1] < start[i]))
    
    # Add constraints for Amber's schedule
    for i in range(len(days)):
        for j in amber_schedule.get(days[i], []):
            s.add(Or(start[i] + j[0] > end[i] + j[1], start[i] + j[0] < start[i], end[i] + j[1] < start[i]))
    
    # Solve the constraints
    s.check()
    
    # Get the solution
    m = s.model()
    
    # Print the solution
    day_index = 0
    for i in range(len(days)):
        if m[day[i]].as_bool():
            day_index = i
            break
    
    start_time = m[start[day_index]].as_long() // 60
    end_time = m[end[day_index]].as_long() // 60
    
    print(f'SOLUTION:')
    print(f'Day: {days[day_index]}')
    print(f'Start Time: {start_time:02d}:00')
    print(f'End Time: {end_time:02d}:00')

# Example usage
ronald_schedule = {
    'Monday': [(10 * 60, 30 * 60), (12 * 60, 30 * 60), (15 * 60, 30 * 60)],
    'Tuesday': [(9 * 60, 30 * 60), (12 * 60, 30 * 60), (15 * 60, 30 * 60)],
    'Wednesday': [(9 * 30, 60 * 30), (11 * 60, 60 * 60), (12 * 30, 60 * 30), (13 * 30, 60 * 30), (16 * 30, 60 * 30)]
}

amber_schedule = {
    'Monday': [(9 * 60, 30 * 60), (10 * 60, 30 * 60), (11 * 30, 60 * 60), (12 * 30, 14 * 60), (14 * 30, 60 * 30), (15 * 30, 60 * 60)],
    'Tuesday': [(9 * 60, 30 * 60), (10 * 60, 11 * 60), (12 * 60, 30 * 60), (13 * 30, 15 * 60), (16 * 30, 60 * 60)],
    'Wednesday': [(9 * 60, 30 * 60), (10 * 60, 30 * 60), (11 * 60, 13 * 30), (15 * 60, 30 * 60)]
}

schedule_meeting(ronald_schedule, amber_schedule, 30 * 60)