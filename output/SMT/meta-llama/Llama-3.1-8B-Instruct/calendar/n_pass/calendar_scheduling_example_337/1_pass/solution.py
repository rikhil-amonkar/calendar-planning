from z3 import *

def schedule_meeting(schedules, meeting_duration):
    # Create a Z3 solver
    solver = Solver()

    # Define the variables
    days = ['Monday']
    hours = range(9, 17)
    minutes = range(0, 60, 30)
    participants = list(schedules.keys())

    # Create variables for the start time
    start_time = [Int(f'start_time_{i}') for i in participants]

    # Add constraints for each participant
    for i, participant in enumerate(participants):
        for time in schedules[participant]:
            # Convert time to minutes
            start = time[0] * 60 + time[1]
            end = (time[0] + 1) * 60 + time[2] if time[2]!= 0 else (time[0] + 1) * 60
            # Add constraints
            solver.add(Or([start_time[i] < start, start_time[i] > end]))
            solver.add(And([start_time[i] >= 9 * 60, start_time[i] <= 17 * 60]))

    # Add constraint for meeting duration
    for i in participants:
        solver.add(And([start_time[i] + meeting_duration * 30 >= 9 * 60, start_time[i] + meeting_duration * 30 <= 17 * 60]))

    # Add constraint for overlapping meetings
    for i in range(len(participants)):
        for j in range(i + 1, len(participants)):
            solver.add(Or([start_time[i] > start_time[j] + meeting_duration * 30, start_time[j] > start_time[i] + meeting_duration * 30]))

    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        day = 'Monday'
        start_time = model[start_time[0]].as_long() // 60
        end_time = (model[start_time[0]].as_long() // 60) + meeting_duration
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_time:02d}:00\nEnd Time: {end_time:02d}:00'
    else:
        return 'No solution found'

schedules = {
    'John': [(11, 30), (12, 0), (14, 0), (14, 30)],
    'Megan': [(12, 0), (12, 30), (14, 0), (15, 0), (15, 30)],
    'Brandon': [],
    'Kimberly': [(9, 0), (9, 30), (10, 0), (10, 30), (11, 0), (14, 30), (15, 0), (16, 0), (16, 30)],
    'Sean': [(10, 0), (11, 0), (11, 30), (14, 0), (15, 0), (15, 30)],
    'Lori': [(9, 0), (9, 30), (10, 30), (12, 0), (13, 0), (14, 30), (16, 0), (16, 30)]
}

meeting_duration = 1

print(schedule_meeting(schedules, meeting_duration))