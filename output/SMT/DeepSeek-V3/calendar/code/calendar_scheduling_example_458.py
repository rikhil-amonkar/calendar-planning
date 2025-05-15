from z3 import *

def find_meeting_time():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # 30 minutes

    # Busy slots for each participant in minutes since 9:00
    melissa_busy = [
        (60, 120),      # 10:00-11:00
        (150, 240),     # 12:30-14:00
        (360, 390)      # 15:00-15:30
    ]
    
    gregory_busy = [
        (150, 180),     # 12:30-13:00
        (390, 420)      # 15:30-16:00
    ]
    
    victoria_busy = [
        (0, 30),        # 9:00-9:30
        (90, 150),      # 10:30-11:30
        (240, 300),     # 13:00-14:00
        (330, 360),     # 14:30-15:00
        (390, 450)      # 15:30-16:30
    ]
    
    thomas_busy = [
        (60, 180),      # 10:00-12:00
        (150, 180),     # 12:30-13:00
        (330, 420)      # 14:30-16:00
    ]
    
    jennifer_busy = [
        (0, 30),        # 9:00-9:30
        (60, 90),       # 10:00-10:30
        (120, 240),     # 11:00-13:00
        (270, 330),     # 13:30-14:30
        (360, 390),     # 15:00-15:30
        (420, 450)      # 16:00-16:30
    ]

    # Create a Z3 solver instance
    s = Solver()

    # The meeting start time (in minutes since 9:00)
    meeting_start = Int('meeting_start')
    
    # Constraints: meeting must be within work hours and have enough duration
    s.add(meeting_start >= 0)
    s.add(meeting_start + meeting_duration <= work_end - work_start)

    # Wayne prefers to avoid meetings before 14:00 (300 minutes since 9:00)
    s.add(meeting_start >= 300)

    # Function to check if a time slot overlaps with any busy slot
    def is_free(time, busy_slots):
        return And([Or(time + meeting_duration <= start, time >= end) for start, end in busy_slots])

    # Add constraints that the meeting time must be free for all participants
    s.add(is_free(meeting_start, melissa_busy))
    s.add(is_free(meeting_start, gregory_busy))
    s.add(is_free(meeting_start, victoria_busy))
    s.add(is_free(meeting_start, thomas_busy))
    s.add(is_free(meeting_start, jennifer_busy))

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