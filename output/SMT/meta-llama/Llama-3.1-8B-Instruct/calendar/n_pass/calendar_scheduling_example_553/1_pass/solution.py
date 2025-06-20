from z3 import *

def schedule_meeting():
    # Define the day and time slots
    day = 'Monday'
    start_time = 9 * 60  # 9:00 in minutes
    end_time = 17 * 60  # 17:00 in minutes
    time_slots = [i for i in range(start_time, end_time)]

    # Define the meeting duration
    meeting_duration = 30  # 30 minutes

    # Define the constraints for Eric's schedule
    eric_blocked = [12 * 60, 13 * 60, 14 * 60, 15 * 60]  # 12:00, 13:00, 14:00, 15:00 in minutes

    # Define the constraints for Henry's schedule
    henry_blocked = [9 * 60 + 30, 10 * 60, 10 * 60 + 30, 11 * 60 + 30, 12 * 60 + 30, 13 * 60, 14 * 60 + 30, 15 * 60, 16 * 60]  # 9:30, 10:00, 10:30, 11:00, 11:30, 12:30, 13:30, 14:30, 15:00, 16:00 in minutes
    henry_preferences = [i for i in henry_blocked if i < 10 * 60 + 30]  # Henry prefers not to meet after 10:00

    # Create a Z3 solver
    s = Solver()

    # Define the variables
    time = Int('time')
    s.add(And(time >= start_time, time <= end_time))  # Time should be within the work hours

    # Add constraints for Eric's schedule
    for block in eric_blocked:
        s.add(Or(time < block, time > block + meeting_duration))  # Time should not overlap with Eric's blocked times

    # Add constraints for Henry's schedule
    for block in henry_blocked:
        s.add(Or(time < block, time > block + meeting_duration))  # Time should not overlap with Henry's blocked times
    for pref in henry_preferences:
        s.add(Or(time < pref, time > pref + meeting_duration))  # Time should not overlap with Henry's preferred times

    # Check if there is a solution
    if s.check() == sat:
        # Get the solution
        model = s.model()
        time_value = model[time]
        start_time_value = time_value - meeting_duration
        end_time_value = time_value

        # Print the solution
        print(f"SOLUTION:")
        print(f"Day: {day}")
        print(f"Start Time: {start_time_value // 60:02d}:{start_time_value % 60:02d}")
        print(f"End Time: {end_time_value // 60:02d}:{end_time_value % 60:02d}")
    else:
        print("No solution found")

schedule_meeting()