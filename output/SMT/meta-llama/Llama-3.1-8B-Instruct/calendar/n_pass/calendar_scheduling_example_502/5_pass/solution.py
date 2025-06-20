from z3 import *

def schedule_meeting(jack_schedule, charlotte_schedule, meeting_duration, day, preferences=None):
    # Create Z3 solver
    solver = Solver()

    # Define variables for start time
    start_time = Int('start_time')

    # Define constraints for start time
    start_time >= 0
    start_time <= 1439  # 1439 minutes in a day (23:59)

    # Convert schedules to minutes
    jack_schedule_minutes = [(t[0]*60) + t[1] for t in jack_schedule]
    charlotte_schedule_minutes = [(t[0]*60) + t[1] for t in charlotte_schedule]

    # Convert meeting duration to minutes
    meeting_duration_minutes = meeting_duration * 60

    # Define constraints for start time based on schedules
    for t in jack_schedule_minutes:
        solver.add(Or(start_time < t, start_time + meeting_duration_minutes <= t))
    for t in charlotte_schedule_minutes:
        solver.add(Or(start_time < t, start_time + meeting_duration_minutes <= t))

    # Add preference constraints if available
    if preferences:
        for pref in preferences:
            solver.add(start_time >= pref[0] * 60 + pref[1])

    # Add constraint for end time
    solver.add(start_time + meeting_duration_minutes <= 1439)

    # Add constraints for available time slots
    available_time_slots = [
        (9, 30, 10, 30),
        (10, 30, 12, 0),
        (12, 30, 13, 0),
        (13, 0, 14, 0),
        (14, 30, 15, 59),
        (16, 30, 17, 0),
        (9, 0, 9, 30),
        (11, 30, 12, 30),
        (14, 0, 14, 30),
        (16, 0, 16, 30)
    ]
    for t in available_time_slots:
        start = t[0] * 60 + t[1]
        end = t[2] * 60 + t[3]
        solver.add(Or(start_time < start, start_time + meeting_duration_minutes <= end))

    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        start_time_value = model[start_time].as_long()
        end_time_value = start_time_value + meeting_duration_minutes
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_time_value // 60:02d}:{start_time_value % 60:02d}\nEnd Time: {end_time_value // 60:02d}:{end_time_value % 60:02d}'
    else:
        return 'No solution found'

# Example usage
jack_schedule = [(9, 30), (11, 0), (12, 30), (14, 0), (16, 0)]
charlotte_schedule = [(9, 30), (10, 30), (12, 30), (14, 0), (16, 0)]
meeting_duration = 0.5
day = 'Monday'
preferences = [(12, 30)]

print(schedule_meeting(jack_schedule, charlotte_schedule, meeting_duration, day, preferences))