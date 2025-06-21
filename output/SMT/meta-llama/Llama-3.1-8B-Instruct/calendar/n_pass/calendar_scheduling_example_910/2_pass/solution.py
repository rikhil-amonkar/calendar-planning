from z3 import *

def schedule_meeting(bryan_schedule, nicholas_schedule, duration, day, preference):
    # Create Z3 solver
    s = Solver()

    # Define variables for day and time
    days = [Bool(f'day_{i}') for i in range(5)]
    s.add(Or(days))

    times = [Int(f'time_{i}') for i in range(24)]
    for i, time in enumerate(times):
        s.add(time >= 0)
        s.add(time < 24)

    # Define variables for meeting
    meeting_day = Int('meeting_day')
    meeting_start_time = Int('meeting_start_time')
    meeting_end_time = Int('meeting_end_time')

    # Define constraints for day
    s.add(meeting_day >= 0)
    s.add(meeting_day < 5)

    # Define constraints for time
    s.add(meeting_start_time >= 0)
    s.add(meeting_start_time < 24)
    s.add(meeting_end_time >= 0)
    s.add(meeting_end_time < 24)

    # Define constraints for duration
    s.add(meeting_end_time - meeting_start_time == duration)

    # Define constraints for existing schedules
    for i, day in enumerate(days):
        for j, time in enumerate(times):
            if (i, j) in bryan_schedule:
                s.add(Not(day))
            if (i, j) in nicholas_schedule:
                s.add(Not(day))

    # Define constraints for preferences
    s.add(Not(days[0]))  # Nicholas prefers not to meet on Monday
    s.add(Not(days[3]))  # Nicholas prefers not to meet on Thursday
    s.add(Not(days[4]))  # Bryan prefers not to meet on Friday
    s.add(Not(days[2]))  # Bryan prefers not to meet on Tuesday

    # Solve the problem
    if s.check() == sat:
        model = s.model()
        day = model[meeting_day].as_long()
        start_time = model[meeting_start_time].as_long()
        end_time = model[meeting_end_time].as_long()
        return f'Day: {day}\nStart Time: {str(start_time).zfill(2)}:00\nEnd Time: {str(end_time).zfill(2)}:00'
    else:
        return 'No solution found'

# Existing schedules for Bryan and Nicholas
bryan_schedule = [
    (3, 9, 30),
    (3, 12, 30),
    (4, 10, 30),
    (4, 14, 0)
]

nicholas_schedule = [
    (0, 11, 30),
    (0, 13, 0, 15, 30),
    (1, 9, 0),
    (1, 11, 0, 13, 30),
    (1, 14, 0, 16, 30),
    (2, 9, 0),
    (2, 10, 0),
    (2, 11, 30, 13, 30),
    (2, 14, 0),
    (2, 15, 0, 16, 30),
    (3, 10, 30, 11, 30),
    (3, 12, 0, 12, 30),
    (3, 15, 0, 15, 30),
    (3, 16, 30, 17, 0),
    (4, 9, 0),
    (4, 11, 0),
    (4, 12, 0),
    (4, 12, 30, 14, 30),
    (4, 15, 30, 16, 0),
    (4, 16, 30, 17, 0)
]

# Meeting duration
duration = 1

# Day and preference
day = 2
preference = True

print(schedule_meeting(bryan_schedule, nicholas_schedule, duration, day, preference))