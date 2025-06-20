from z3 import *

def solve_meeting():
    # Define the days of the week
    days = ['Monday', 'Tuesday', 'Wednesday']

    # Define the start and end times of the work hours
    start_time = 9
    end_time = 17

    # Define the meeting duration
    meeting_duration = 30

    # Define the constraints for Samuel's schedule
    samuel_schedule = [
        (Monday, 10, 30),
        (Monday, 12, 0),
        (Monday, 13, 0, 15, 0),
        (Monday, 15, 30, 16, 30),
        (Tuesday, 9, 0, 12, 0),
        (Tuesday, 14, 0, 15, 30),
        (Tuesday, 16, 30, 17, 0),
        (Wednesday, 10, 30),
        (Wednesday, 11, 30, 12, 0),
        (Wednesday, 12, 30, 13, 0),
        (Wednesday, 14, 0, 14, 30),
        (Wednesday, 15, 0, 16, 0)
    ]

    # Define the constraints for Larry's schedule
    larry_schedule = []

    # Define the preferences
    larry_preference = Wednesday
    samuel_preference = Tuesday

    # Create a solver
    s = Solver()

    # Define the variables
    day = Int('day')
    start_hour = Int('start_hour')
    start_minute = Int('start_minute')
    end_hour = Int('end_hour')
    end_minute = Int('end_minute')

    # Define the constraints
    s.add(day >= 0)
    s.add(day < len(days))
    s.add(start_hour >= start_time)
    s.add(start_hour < end_time)
    s.add(start_minute >= 0)
    s.add(start_minute < 60)
    s.add(end_hour >= start_hour)
    s.add(end_hour < end_time)
    s.add(end_minute >= 0)
    s.add(end_minute < 60)

    # Add constraints for the meeting duration
    s.add((start_hour * 60 + start_minute + meeting_duration * 60) == (end_hour * 60 + end_minute))

    # Add constraints for Samuel's schedule
    for d, h1, m1, h2 = samuel_schedule:
        if d == Monday:
            s.add(Or(start_hour > h1, start_hour > h2, (start_hour == h1 and start_minute > m1), (start_hour == h2 and start_minute > m2)))
        elif d == Tuesday:
            s.add(Or(start_hour > h1, start_hour > h2, (start_hour == h1 and start_minute > m1), (start_hour == h2 and start_minute > m2)))
        else:
            s.add(Or(start_hour > h1, start_hour > h2, (start_hour == h1 and start_minute > m1), (start_hour == h2 and start_minute > m2)))

    # Add constraints for Larry's schedule
    for d in days:
        s.add(Or(start_hour > h1, start_hour > h2, (start_hour == h1 and start_minute > m1), (start_hour == h2 and start_minute > m2)))

    # Add constraints for the preferences
    s.add(Or(day!= larry_preference, start_hour > 8))
    s.add(Or(day!= samuel_preference, start_hour > 8))

    # Add constraints for the earliest availability
    s.add(start_hour * 60 + start_minute >= 9 * 60)

    # Check the solution
    if s.check() == sat:
        model = s.model()
        day_value = days[model[day].as_long()]
        start_hour_value = model[start_hour].as_long()
        start_minute_value = model[start_minute].as_long()
        end_hour_value = model[end_hour].as_long()
        end_minute_value = model[end_minute].as_long()
        return f"SOLUTION:\nDay: {day_value}\nStart Time: {start_hour_value:02d}:{start_minute_value:02d}\nEnd Time: {end_hour_value:02d}:{end_minute_value:02d}"
    else:
        return "No solution found"

print(solve_meeting())