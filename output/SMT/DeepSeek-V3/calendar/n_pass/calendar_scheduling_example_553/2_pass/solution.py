from z3 import *

def solve_scheduling_problem():
    # Initialize the solver
    s = Solver()

    # Define the work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes (exactly 0.5 hours)

    # Define the possible start times within work hours
    start_time = Int('start_time')
    s.add(start_time >= work_start)
    s.add(start_time <= work_end - meeting_duration)

    # Eric's blocked times (in minutes)
    eric_blocked = [
        (12 * 60, 13 * 60),  # 12:00 to 13:00
        (14 * 60, 15 * 60)   # 14:00 to 15:00
    ]

    # Henry's meetings (in minutes)
    henry_meetings = [
        (9 * 60 + 30, 10 * 60),      # 9:30 to 10:00
        (10 * 60 + 30, 11 * 60),     # 10:30 to 11:00
        (11 * 60 + 30, 12 * 60 + 30), # 11:30 to 12:30
        (13 * 60, 13 * 60 + 30),     # 13:00 to 13:30
        (14 * 60 + 30, 15 * 60),     # 14:30 to 15:00
        (16 * 60, 17 * 60)           # 16:00 to 17:00
    ]

    # Add constraints for Eric's schedule
    for block_start, block_end in eric_blocked:
        s.add(Or(
            start_time + meeting_duration <= block_start,
            start_time >= block_end
        ))

    # Add constraints for Henry's schedule
    for meeting_start, meeting_end in henry_meetings:
        s.add(Or(
            start_time + meeting_duration <= meeting_start,
            start_time >= meeting_end
        ))

    # Henry's preference: not after 10:00 (i.e., start_time + duration <= 10:00)
    preference_start = 10 * 60
    # First try to satisfy the preference
    s.push()
    s.add(start_time + meeting_duration <= preference_start)
    if s.check() == sat:
        m = s.model()
        start_min = m[start_time].as_long()
        start_hour = start_min // 60
        start_min = start_min % 60
        end_min = start_min + meeting_duration
        end_hour = start_hour + (end_min // 60)
        end_min = end_min % 60

        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hour:02d}:{start_min:02d}")
        print(f"End Time: {end_hour:02d}:{end_min:02d}")
        return
    s.pop()

    # If no solution with preference, try without it
    if s.check() == sat:
        m = s.model()
        start_min = m[start_time].as_long()
        start_hour = start_min // 60
        start_min = start_min % 60
        end_min = start_min + meeting_duration
        end_hour = start_hour + (end_min // 60)
        end_min = end_min % 60

        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hour:02d}:{start_min:02d}")
        print(f"End Time: {end_hour:02d}:{end_min:02d}")
    else:
        print("No solution found")

solve_scheduling_problem()