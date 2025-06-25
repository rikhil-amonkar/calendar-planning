from z3 import *

def schedule_meeting(day, schedules, duration, preferences=None):
    # Define the time slots
    start_time = 9 * 60  # 9:00
    end_time = 17 * 60  # 17:00
    time_slots = [i for i in range(start_time, end_time, 30)]

    # Create the solver
    s = Solver()

    # Create the variables
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Add the constraints
    s.add(meeting_start >= start_time)
    s.add(meeting_start <= end_time - duration)
    s.add(meeting_end >= meeting_start + duration)
    s.add(meeting_end <= end_time)

    # Add the constraints for each participant
    for participant, schedule in schedules.items():
        for time in schedule:
            s.add(meeting_start + duration > time[0] * 60 + time[1])
            s.add(meeting_end < (time[0] + 1) * 60 + time[1])

    # Add the preference constraint
    if preferences is not None:
        for participant, pref in preferences.items():
            for time in pref:
                s.add(meeting_start + duration > time[0] * 60 + time[1])

    # Add the constraint that the meeting duration is 30 minutes
    s.add(meeting_end - meeting_start == duration)

    # Solve the problem
    if s.check() == sat:
        model = s.model()
        meeting_start_value = model[meeting_start].as_long()
        meeting_end_value = model[meeting_end].as_long()
        return f'SOLUTION:\nDay: {day}\nStart Time: {meeting_start_value // 60:02d}:{meeting_start_value % 60:02d}\nEnd Time: {meeting_end_value // 60:02d}:{meeting_end_value % 60:02d}'
    else:
        return 'No solution found'

# Define the schedules and preferences
schedules = {
    'Adam': [(14, 0), (15, 0)],
    'John': [(13, 0), (13, 30), (14, 0), (14, 30), (15, 30), (16, 0), (16, 30), (17, 0)],
    'Stephanie': [(9, 30), (10, 0), (10, 30), (11, 0), (11, 30), (16, 0), (16, 30), (17, 0)],
    'Anna': [(9, 30), (12, 0), (12, 30), (13, 0), (15, 30), (16, 30), (17, 0)]
}
preferences = {
    'Anna': [(9, 30), (12, 0)]
}

# Call the function
print(schedule_meeting('Monday', schedules, 30, preferences))