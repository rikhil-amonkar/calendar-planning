from z3 import *

def find_meeting_time():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 60  # 60 minutes

    # Ryan's busy slots in minutes since 9:00
    ryan_busy = [
        (0, 30),        # 9:00-9:30
        (210, 240)      # 12:30-13:00
    ]
    
    # Denise's busy slots in minutes since 9:00
    denise_busy = [
        (30, 90),       # 9:30-10:30
        (180, 240),     # 12:00-13:00
        (330, 450)      # 14:30-16:30
    ]

    # Create a Z3 solver instance
    s = Solver()

    # The meeting start time (in minutes since 9:00)
    meeting_start = Int('meeting_start')
    
    # Constraints: meeting must be within work hours and have enough duration
    s.add(meeting_start >= 0)
    s.add(meeting_start + meeting_duration <= work_end - work_start)

    # Denise does not want to meet after 12:30 (210 minutes since 9:00)
    s.add(meeting_start + meeting_duration <= 210)

    # Function to check if a time slot overlaps with any busy slot
    def is_free(time, busy_slots):
        return And([Or(time + meeting_duration <= start, time >= end) for start, end in busy_slots])

    # Add constraints that the meeting time must be free for Ryan and Denise
    s.add(is_free(meeting_start, ryan_busy))
    s.add(is_free(meeting_start, denise_busy))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_minutes = m[meeting_start].as_long()
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        print(f"Monday, {start_hour:02d}:{start_minute:02d} to {end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable meeting time found.")

find_meeting_time()