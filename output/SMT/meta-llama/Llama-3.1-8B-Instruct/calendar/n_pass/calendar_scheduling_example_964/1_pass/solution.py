from z3 import *

def schedule_meeting(betty_schedule, megan_schedule, meeting_duration, preferred_days=None):
    # Create Z3 variables for the meeting day and time
    days = [Int(f'day') for _ in range(5)]  # Monday to Friday
    for i, day in enumerate(days):
        day.value = i + 1  # Assign values to the days (1-5)
    
    start_time = [Int(f'start_time') for _ in range(5)]
    end_time = [Int(f'end_time') for _ in range(5)]
    
    # Define the meeting duration
    meeting_duration = 60  # in minutes
    
    # Define the constraints for the meeting day
    if preferred_days is not None:
        for day in days:
            if day.value not in preferred_days:
                day.eq(0)  # If the day is not preferred, set it to 0
    
    # Define the constraints for the meeting time
    for day in days:
        start_time[day.value - 1].ge(9 * 60)  # Start time >= 9:00
        start_time[day.value - 1].le(16 * 60)  # Start time <= 16:00
        end_time[day.value - 1].ge(start_time[day.value - 1])  # End time >= start time
        end_time[day.value - 1].le(17 * 60)  # End time <= 17:00
        end_time[day.value - 1].eq(start_time[day.value - 1] + meeting_duration)  # End time = start time + meeting duration
    
    # Define the constraints for Betty's schedule
    betty_constraints = []
    for day in days:
        for time in betty_schedule[day.value - 1]:
            start, end = time.split('-')
            start = int(start[:2]) * 60 + int(start[3:])
            end = int(end[:2]) * 60 + int(end[3:])
            constraint = And(start_time[day.value - 1] > start, start_time[day.value - 1] < end, end_time[day.value - 1] > start, end_time[day.value - 1] < end)
            betty_constraints.append(constraint)
    
    # Define the constraints for Megan's schedule
    megan_constraints = []
    for day in days:
        for time in megan_schedule[day.value - 1]:
            start, end = time.split('-')
            start = int(start[:2]) * 60 + int(start[3:])
            end = int(end[:2]) * 60 + int(end[3:])
            constraint = And(start_time[day.value - 1] > start, start_time[day.value - 1] < end, end_time[day.value - 1] > start, end_time[day.value - 1] < end)
            megan_constraints.append(constraint)
    
    # Define the constraint for Betty not meeting on Wednesday and Thursday
    for day in days:
        if day.value in [3, 4]:  # Wednesday and Thursday
            start_time[day.value - 1].eq(0)  # Set start time to 0 (invalid)
            end_time[day.value - 1].eq(0)  # Set end time to 0 (invalid)
    
    # Create the Z3 solver and add the constraints
    solver = Solver()
    for constraint in betty_constraints:
        solver.add(constraint)
    for constraint in megan_constraints:
        solver.add(constraint)
    
    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        day = model[days[0]]
        start_time_value = model[start_time[day.value - 1]]
        end_time_value = model[end_time[day.value - 1]]
        day_str = 'Monday' if day == 1 else 'Tuesday' if day == 2 else 'Wednesday' if day == 3 else 'Thursday' if day == 4 else 'Friday'
        start_time_str = f'{start_time_value // 60:02d}:{start_time_value % 60:02d}'
        end_time_str = f'{end_time_value // 60:02d}:{end_time_value % 60:02d}'
        return f'SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}'
    else:
        return 'No solution found'

# Define the schedules for Betty and Megan
betty_schedule = [
    ['09:00-09:30', '10:00-10:30', '11:30-12:30', '16:00-16:30'],
    ['09:30-10:00', '10:30-11:00', '12:00-12:30', '13:30-15:00', '16:30-17:00'],
    ['13:30-14:00', '14:30-15:00'],
    [],
    ['09:00-10:00', '11:30-12:00', '12:30-13:00', '14:30-15:00']
]

megan_schedule = [
    ['09:00-17:00'],
    ['09:00-09:30', '10:00-10:30', '12:00-14:00', '15:00-15:30', '16:00-16:30'],
    ['09:30-10:30', '11:00-11:30', '12:30-13:00', '13:30-14:30', '15:30-17:00'],
    ['09:00-10:30', '11:30-14:00', '14:30-15:00', '15:30-16:30'],
    ['09:00-17:00']
]

# Define the meeting duration
meeting_duration = 60  # in minutes

# Find a solution
print(schedule_meeting(betty_schedule, megan_schedule, meeting_duration, preferred_days=[1, 2, 5]))