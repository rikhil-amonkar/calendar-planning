from z3 import *

def find_meeting_time():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # 30 minutes

    # Harold's busy slots in minutes since 9:00 for Monday and Tuesday
    harold_monday_busy = [
        (0, 60),         # 9:00-10:00
        (90, 480)        # 10:30-17:00
    ]
    
    harold_tuesday_busy = [
        (0, 30),         # 9:00-9:30
        (90, 150),       # 10:30-11:30
        (210, 270),      # 12:30-13:30
        (330, 390),      # 14:30-15:30
        (420, 480)       # 16:00-17:00
    ]

    # Create a Z3 solver instance
    s = Solver()

    # The meeting day (0 for Monday, 1 for Tuesday)
    day = Int('day')
    s.add(Or(day == 0, day == 1))

    # The meeting start time (in minutes since 9:00)
    meeting_start = Int('meeting_start')
    
    # Constraints: meeting must be within work hours and have enough duration
    s.add(meeting_start >= 0)
    s.add(meeting_start + meeting_duration <= work_end - work_start)

    # Function to check if a time slot overlaps with any busy slot
    def is_free(time, busy_slots):
        return And([Or(time + meeting_duration <= start, time >= end) for start, end in busy_slots])

    # Add constraints based on the day
    # If Monday, avoid Harold's busy slots and respect preference to avoid Monday
    monday_constraint = And(day == 0, is_free(meeting_start, harold_monday_busy))
    # If Tuesday, avoid Harold's busy slots and respect preference to avoid before 14:30
    tuesday_constraint = And(day == 1, is_free(meeting_start, harold_tuesday_busy), meeting_start >= 330 - work_start)

    # Prefer Tuesday over Monday
    s.add(Or(tuesday_constraint, monday_constraint))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_minutes = m[meeting_start].as_long()
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        day_name = "Monday" if day_val == 0 else "Tuesday"
        print(f"{day_name}, {start_hour:02d}:{start_minute:02d} to {end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable meeting time found.")

find_meeting_time()