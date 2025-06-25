from z3 import *

def schedule_meeting():
    # Define the days of the week
    days = ['Monday', 'Tuesday']
    monday = 0
    tuesday = 1

    # Define the start and end times of the work hours
    start_time = 9
    end_time = 17

    # Define the meeting duration
    meeting_duration = 0.5  # in hours

    # Define the constraints for Harold's schedule
    harold_schedule = [
        (monday, 9, 10),  # Monday 9:00-10:00
        (monday, 10.5, 17),  # Monday 10:30-17:00
        (tuesday, 9, 9.5),  # Tuesday 9:00-9:30
        (tuesday, 10.5, 11.5),  # Tuesday 10:30-11:30
        (tuesday, 12.5, 13.5),  # Tuesday 12:30-13:30
        (tuesday, 14.5, 15.5),  # Tuesday 14:30-15:30
        (tuesday, 16, 17)  # Tuesday 16:00-17:00
    ]

    # Define the constraints for Harold's preferences
    harold_preferences = [
        (monday, 0),  # Harold prefers not to meet on Monday
        (tuesday, 0, 14.5)  # Harold prefers not to meet on Tuesday before 14:30
    ]

    # Define the solver
    s = Solver()

    # Define the variables
    day = Int('day')
    start = Real('start')
    end = Real('end')

    # Define the constraints
    s.add(day in [monday, tuesday])  # day is either Monday or Tuesday
    s.add(start >= 9)  # start time is at least 9:00
    s.add(start <= 17)  # start time is at most 17:00
    s.add(end >= start + 0.5)  # end time is at least 30 minutes after start time
    s.add(end <= 17)  # end time is at most 17:00

    # Add constraints for Harold's schedule
    for d, st, en in harold_schedule:
        s.add(If(day == d, st <= start, True))
        s.add(If(day == d, end <= en, True))

    # Add constraints for Harold's preferences
    for d, st in harold_preferences:
        s.add(If(day == d, start >= st, True))

    # Solve the constraints
    s.check()

    # Get the solution
    m = s.model()

    # Print the solution
    day = days[m[day].as_long()]
    start = int(m[start].as_real().numerator / m[start].as_real().denominator * 60)
    end = int(m[end].as_real().numerator / m[end].as_real().denominator * 60)
    print(f"SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start:02d}:00")
    print(f"End Time: {int(end + 0.5):02d}:00")

schedule_meeting()