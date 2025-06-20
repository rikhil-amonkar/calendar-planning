from z3 import *

def schedule_meeting(schedules, meeting_duration, preferences=None):
    # Create a Z3 solver
    solver = Solver()

    # Create variables for start and end times
    start_times = {}
    end_times = {}
    for name, schedule in schedules.items():
        start_times[name] = [Int(f'{name}_start_{i}') for i in range(len(schedule))]
        end_times[name] = [Int(f'{name}_end_{i}') for i in range(len(schedule))]
        for i in range(len(schedule)):
            # Add constraints for each time slot
            solver.add(start_times[name][i] >= schedule[i][0])
            solver.add(start_times[name][i] < schedule[i][1])
            solver.add(end_times[name][i] > start_times[name][i])
            solver.add(end_times[name][i] <= schedule[i][1])

    # Create variables for meeting start and end times
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Add constraints for meeting duration
    solver.add(meeting_end - meeting_start == meeting_duration)

    # Add constraints for each participant's schedule
    for name, schedule in schedules.items():
        for i in range(len(schedule)):
            # Add constraints for each time slot
            solver.add(meeting_start >= schedule[i][0])
            solver.add(meeting_start < schedule[i][1])
            solver.add(meeting_end > schedule[i][0])
            solver.add(meeting_end <= schedule[i][1])

    # Add constraints for preferences
    if preferences is not None:
        for name, pref in preferences.items():
            if pref:
                solver.add(meeting_start >= pref)

    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        day = 'Monday'
        start_time = model[meeting_start].as_long()
        end_time = model[meeting_end].as_long()
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_time:02d}:{(start_time % 100):02d}\nEnd Time: {end_time:02d}:{(end_time % 100):02d}'
    else:
        return 'No solution found'

# Define the schedules
schedules = {
    'Natalie': [(9, 17)],
    'David': [(11, 12), (14, 15)],
    'Douglas': [(9, 10), (11, 12), (13, 13, 30), (14, 15)],
    'Ralph': [(9, 9, 30), (10, 11), (11, 12, 30), (13, 15), (15, 16), (16, 30, 17)],
    'Jordan': [(9, 10), (12, 12, 30), (13, 13, 30), (14, 15), (15, 17)]
}

# Define the meeting duration
meeting_duration = 30

# Define the preferences
preferences = {
    'David': (14, 17)
}

print(schedule_meeting(schedules, meeting_duration, preferences))