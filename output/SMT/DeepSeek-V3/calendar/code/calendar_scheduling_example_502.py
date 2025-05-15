from z3 import *

def find_meeting_time():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # 30 minutes

    # Jack's busy slots in minutes since 9:00
    jack_busy = [
        (30, 90),         # 9:30-10:30
        (120, 150),       # 11:00-11:30
        (210, 240),       # 12:30-13:00
        (300, 330),       # 14:00-14:30
        (420, 450)        # 16:00-16:30
    ]
    
    # Charlotte's busy slots in minutes since 9:00
    charlotte_busy = [
        (30, 60),         # 9:30-10:00
        (90, 180),        # 10:30-12:00
        (210, 270),       # 12:30-13:30
        (300, 420)        # 14:00-16:00
    ]

    # Create a Z3 solver instance
    s = Solver()

    # The meeting start time (in minutes since 9:00)
    meeting_start = Int('meeting_start')
    
    # Constraints: meeting must be within work hours and have enough duration
    s.add(meeting_start >= 0)
    s.add(meeting_start + meeting_duration <= work_end - work_start)

    # Jack prefers to avoid meetings after 12:30 (210 minutes since 9:00)
    s.add(meeting_start + meeting_duration <= 210)

    # Function to check if a time slot overlaps with any busy slot
    def is_free(time, busy_slots):
        return And([Or(time + meeting_duration <= start, time >= end) for start, end in busy_slots])

    # Add constraints that the meeting time must be free for both Jack and Charlotte
    s.add(is_free(meeting_start, jack_busy))
    s.add(is_free(meeting_start, charlotte_busy))

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