from z3 import *

def schedule_meeting(eugene_schedule, eric_schedule, meeting_duration, day, avoid_day=False):
    # Create a solver
    solver = Solver()

    # Define variables for the start time
    start_time = [Bool(f'start_{day}_{i}') for i in range(96)]  # 96 intervals in a day (24*4)

    # Add constraints for the start time
    for i in range(96):
        # Ensure the start time is within the work hours
        if i < 9 or i > 71:  # 9:00 to 17:00 in 30-minute intervals
            solver.add(Not(start_time[i]))
        # Ensure the start time is not busy for Eugene
        if i >= 11 and i < 36 and day == 'Monday' and i >= 13*3 and i < 14*3:  # 11:00 to 12:00, 13:30 to 14:00, 14:30 to 15:00 on Monday
            solver.add(Not(start_time[i]))
        elif i >= 11 and i < 36 and day == 'Wednesday' and i >= 11*3 and i < 12*3:  # 11:00 to 11:30 on Wednesday
            solver.add(Not(start_time[i]))
        elif i >= 11 and i < 36 and day == 'Wednesday' and i >= 13*3 and i < 15*3:  # 13:30 to 15:00 on Wednesday
            solver.add(Not(start_time[i]))
        elif i >= 11 and i < 36 and day == 'Thursday' and i >= 11*3 and i < 12*3*2:  # 11:00 to 12:30 on Thursday
            solver.add(Not(start_time[i]))
        elif i >= 10*3 and i < 11 and day == 'Friday':  # 10:30 to 11:00 on Friday
            solver.add(Not(start_time[i]))
        elif i >= 12 and i < 12*2 and day == 'Friday':  # 12:00 to 12:30 on Friday
            solver.add(Not(start_time[i]))
        elif i >= 13 and i < 13*2 and day == 'Friday':  # 13:00 to 13:30 on Friday
            solver.add(Not(start_time[i]))
        # Ensure the start time is not busy for Eric
        if i >= 9 and i < 17 and day == 'Monday':  # 9:00 to 17:00 on Monday
            solver.add(Not(start_time[i]))
        elif i >= 9 and i < 17 and day == 'Tuesday':  # 9:00 to 17:00 on Tuesday
            solver.add(Not(start_time[i]))
        elif i >= 9 and i < 11*3 and day == 'Wednesday':  # 9:00 to 11:30 on Wednesday
            solver.add(Not(start_time[i]))
        elif i >= 12 and i < 14 and day == 'Wednesday':  # 12:00 to 14:00 on Wednesday
            solver.add(Not(start_time[i]))
        elif i >= 14*3 and i < 16*3 and day == 'Wednesday':  # 14:30 to 16:30 on Wednesday
            solver.add(Not(start_time[i]))
        elif i >= 9 and i < 17 and day == 'Thursday':  # 9:00 to 17:00 on Thursday
            solver.add(Not(start_time[i]))
        elif i >= 9 and i < 11 and day == 'Friday':  # 9:00 to 11:00 on Friday
            solver.add(Not(start_time[i]))
        elif i >= 11*3 and i < 17 and day == 'Friday':  # 11:30 to 17:00 on Friday
            solver.add(Not(start_time[i]))
        # Ensure the start time is not on the day Eric wants to avoid
        if avoid_day and day == 'Wednesday':
            for j in range(11*3, 17):
                solver.add(Not(start_time[j]))

    # Add constraints for the end time
    for i in range(96):
        # Ensure the end time is within the work hours
        if i < 9 or i > 71:  # 9:00 to 17:00 in 30-minute intervals
            solver.add(Not(start_time[i]))
        # Ensure the end time is not busy for Eugene
        if i >= 11 and i < 36 and day == 'Monday' and i >= 13*3 and i < 14*3:  # 11:00 to 12:00, 13:30 to 14:00, 14:30 to 15:00 on Monday
            solver.add(Not(start_time[i]))
        elif i >= 11 and i < 36 and day == 'Wednesday' and i >= 11*3 and i < 12*3:  # 11:00 to 11:30 on Wednesday
            solver.add(Not(start_time[i]))
        elif i >= 11 and i < 36 and day == 'Wednesday' and i >= 13*3 and i < 15*3:  # 13:30 to 15:00 on Wednesday
            solver.add(Not(start_time[i]))
        elif i >= 11 and i < 36 and day == 'Thursday' and i >= 11*3 and i < 12*3*2:  # 11:00 to 12:30 on Thursday
            solver.add(Not(start_time[i]))
        elif i >= 10*3 and i < 11 and day == 'Friday':  # 10:30 to 11:00 on Friday
            solver.add(Not(start_time[i]))
        elif i >= 12 and i < 12*2 and day == 'Friday':  # 12:00 to 12:30 on Friday
            solver.add(Not(start_time[i]))
        elif i >= 13 and i < 13*2 and day == 'Friday':  # 13:00 to 13:30 on Friday
            solver.add(Not(start_time[i]))
        # Ensure the end time is not busy for Eric
        if i >= 9 and i < 17 and day == 'Monday':  # 9:00 to 17:00 on Monday
            solver.add(Not(start_time[i]))
        elif i >= 9 and i < 17 and day == 'Tuesday':  # 9:00 to 17:00 on Tuesday
            solver.add(Not(start_time[i]))
        elif i >= 9 and i < 11*3 and day == 'Wednesday':  # 9:00 to 11:30 on Wednesday
            solver.add(Not(start_time[i]))
        elif i >= 12 and i < 14 and day == 'Wednesday':  # 12:00 to 14:00 on Wednesday
            solver.add(Not(start_time[i]))
        elif i >= 14*3 and i < 16*3 and day == 'Wednesday':  # 14:30 to 16:30 on Wednesday
            solver.add(Not(start_time[i]))
        elif i >= 9 and i < 17 and day == 'Thursday':  # 9:00 to 17:00 on Thursday
            solver.add(Not(start_time[i]))
        elif i >= 9 and i < 11 and day == 'Friday':  # 9:00 to 11:00 on Friday
            solver.add(Not(start_time[i]))
        elif i >= 11*3 and i < 17 and day == 'Friday':  # 11:30 to 17:00 on Friday
            solver.add(Not(start_time[i]))
        # Ensure the end time is not on the day Eric wants to avoid
        if avoid_day and day == 'Wednesday':
            for j in range(11*3, 17):
                solver.add(Not(start_time[j]))

    # Add constraints for the meeting duration
    for i in range(96 - meeting_duration):
        # Ensure the start time is not busy for Eugene
        if i >= 11 and i < 36 and day == 'Monday' and i + meeting_duration >= 13*3 and i + meeting_duration < 14*3:  # 11:00 to 12:00, 13:30 to 14:00, 14:30 to 15:00 on Monday
            solver.add(Not(start_time[i]))
        elif i >= 11 and i < 36 and day == 'Wednesday' and i + meeting_duration >= 11*3 and i + meeting_duration < 12*3:  # 11:00 to 11:30 on Wednesday
            solver.add(Not(start_time[i]))
        elif i >= 11 and i < 36 and day == 'Wednesday' and i + meeting_duration >= 13*3 and i + meeting_duration < 15*3:  # 13:30 to 15:00 on Wednesday
            solver.add(Not(start_time[i]))
        elif i >= 11 and i < 36 and day == 'Thursday' and i + meeting_duration >= 11*3 and i + meeting_duration < 12*3*2:  # 11:00 to 12:30 on Thursday
            solver.add(Not(start_time[i]))
        elif i >= 10*3 and i < 11 and day == 'Friday' and i + meeting_duration >= 11 and i + meeting_duration < 11*2:  # 10:30 to 11:00 on Friday
            solver.add(Not(start_time[i]))
        elif i >= 12 and i < 12*2 and day == 'Friday' and i + meeting_duration >= 12 and i + meeting_duration < 12*2:  # 12:00 to 12:30 on Friday
            solver.add(Not(start_time[i]))
        elif i >= 13 and i < 13*2 and day == 'Friday' and i + meeting_duration >= 13 and i + meeting_duration < 13*2:  # 13:00 to 13:30 on Friday
            solver.add(Not(start_time[i]))
        # Ensure the start time is not busy for Eric
        if i >= 9 and i < 17 and day == 'Monday':  # 9:00 to 17:00 on Monday
            solver.add(Not(start_time[i]))
        elif i >= 9 and i < 17 and day == 'Tuesday':  # 9:00 to 17:00 on Tuesday
            solver.add(Not(start_time[i]))
        elif i >= 9 and i < 11*3 and day == 'Wednesday':  # 9:00 to 11:30 on Wednesday
            solver.add(Not(start_time[i]))
        elif i >= 12 and i < 14 and day == 'Wednesday':  # 12:00 to 14:00 on Wednesday
            solver.add(Not(start_time[i]))
        elif i >= 14*3 and i < 16*3 and day == 'Wednesday':  # 14:30 to 16:30 on Wednesday
            solver.add(Not(start_time[i]))
        elif i >= 9 and i < 17 and day == 'Thursday':  # 9:00 to 17:00 on Thursday
            solver.add(Not(start_time[i]))
        elif i >= 9 and i < 11 and day == 'Friday':  # 9:00 to 11:00 on Friday
            solver.add(Not(start_time[i]))
        elif i >= 11*3 and i < 17 and day == 'Friday':  # 11:30 to 17:00 on Friday
            solver.add(Not(start_time[i]))
        # Ensure the end time is not on the day Eric wants to avoid
        if avoid_day and day == 'Wednesday':
            for j in range(11*3, 17):
                solver.add(Not(start_time[j]))

    # Add constraints for the meeting duration
    for i in range(96 - meeting_duration):
        solver.add(start_time[i] == start_time[i + meeting_duration])

    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        day = day
        start_time_index = [i for i, x in enumerate(model.eval(start_time).as_bool_array()) if x][0]
        start_hour = start_time_index // 4
        start_minute = start_time_index % 4 * 30
        end_hour = (start_time_index + meeting_duration) // 4
        end_minute = (start_time_index + meeting_duration) % 4 * 30
        return f'Day: {day}\nStart Time: {start_hour:02d}:{start_minute:02d}\nEnd Time: {end_hour:02d}:{end_minute:02d}'
    else:
        return 'No solution found'

# Define the schedules for Eugene and Eric
eugene_schedule = {
    'Monday': [(11, 12), (13.5, 14), (14.5, 15), (16, 16.5)],
    'Wednesday': [(9, 9.5), (11, 11.5), (12, 12.5), (13.5, 15)],
    'Thursday': [(9.5, 10), (11, 12.5)],
    'Friday': [(10.5, 11), (12, 12.5), (13, 13.5)]
}
eric_schedule = {
    'Monday': [(9, 17)],
    'Tuesday': [(9, 17)],
    'Wednesday': [(9, 11.5), (12, 14), (14.5, 16.5)],
    'Thursday': [(9, 17)],
    'Friday': [(9, 11), (11.5, 17)]
}

# Define the meeting duration
meeting_duration = 0.5

# Find a time that works for everyone's schedule and constraints
for day in ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']:
    solution = schedule_meeting(eugene_schedule, eric_schedule, meeting_duration, day, avoid_day=True)
    if solution!= 'No solution found':
        print(solution)
        break