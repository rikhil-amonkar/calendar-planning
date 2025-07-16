from z3 import *

def solve_scheduling():
    s = Solver()

    # Define the possible days (Monday and Tuesday)
    is_monday = Bool('is_monday')

    # Meeting duration is 30 minutes
    meeting_duration = 30

    # Define the start time in minutes from 9:00 (540 minutes in 24-hour format)
    start_time = Int('start_time')
    work_start = 540  # 9:00 in minutes
    work_end = 1020   # 17:00 in minutes

    # General constraints for work hours
    s.add(start_time >= work_start)
    s.add(start_time + meeting_duration <= work_end)

    # Margaret does not want to meet on Monday
    s.add(Not(is_monday))

    # Margaret's blocked times on Tuesday: 12:00-12:30 (720-750 minutes)
    # But the meeting must start >= 14:30 (870 minutes), so these blocks are irrelevant
    # So no additional Margaret constraints beyond the start time >= 870

    # Alexis's blocked times on Tuesday: 9:00-9:30 (540-570), 10:00-10:30 (600-630), 14:00-16:30 (840-990)
    # The meeting must not overlap with these
    # Since start_time >= 870, possible overlaps are with 14:00-16:30 (840-990)
    # So the meeting must satisfy: start_time + 30 <= 840 or start_time >= 990
    s.add(Or(start_time + meeting_duration <= 840, start_time >= 990))

    # Also, start_time >= 870 (14:30)
    s.add(start_time >= 870)

    # Check for solution
    if s.check() == sat:
        m = s.model()
        day = "Tuesday"
        start_min = m[start_time].as_long()
        start_hour = start_min // 60
        start_minute = start_min % 60
        end_min = start_min + meeting_duration
        end_hour = end_min // 60
        end_minute = end_min % 60

        print("SOLUTION:")
        print(f"Day: {day}")
        print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
        print(f"End Time: {end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

solve_scheduling()