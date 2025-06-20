from z3 import *

def schedule_meeting(eric_schedule, henry_schedule, meeting_duration, preferences):
    # Create Z3 solver
    s = Solver()

    # Define variables
    day = Int('day')
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Add constraints for day
    s.add(day == 1)  # Monday

    # Add constraints for start and end time
    s.add(And(9 * 60 <= start_time, start_time <= 17 * 60))
    s.add(end_time == start_time + meeting_duration * 60)

    # Add constraints for Eric's schedule
    for start, end in eric_schedule:
        s.add(Or(start * 60 > end_time, end * 60 < start_time))

    # Add constraints for Henry's schedule
    for start, end in henry_schedule:
        s.add(Or(start * 60 > end_time, end * 60 < start_time))

    # Add preference constraints
    if preferences:
        for start, end in preferences:
            s.add(Or(start * 60 > end_time, end * 60 < start_time))

    # Add constraint that meeting duration is half an hour
    s.add(meeting_duration == 0.5)

    # Check if a solution exists
    if s.check() == sat:
        # Get the solution
        model = s.model()
        day_value = model[day].as_long()
        start_time_value = model[start_time].as_long()
        end_time_value = model[end_time].as_long()

        # Print the solution
        print(f"SOLUTION:")
        print(f"Day: {day_value}")
        print(f"Start Time: {start_time_value // 60:02d}:{start_time_value % 60:02d}")
        print(f"End Time: {end_time_value // 60:02d}:{end_time_value % 60:02d}")
    else:
        print("No solution exists")

# Example usage
eric_schedule = [(12 * 60, 13 * 60), (14 * 60, 15 * 60)]
henry_schedule = [(9.5 * 60, 10 * 60), (10.5 * 60, 11 * 60), (11.5 * 60, 12.5 * 60), (13 * 60, 13.5 * 60), (14.5 * 60, 15 * 60), (16 * 60, 17 * 60)]
meeting_duration = 0.5
preferences = [(9 * 60, 10 * 60)]

schedule_meeting(eric_schedule, henry_schedule, meeting_duration, preferences)