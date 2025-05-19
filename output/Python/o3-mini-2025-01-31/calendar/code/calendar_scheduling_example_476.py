from datetime import datetime, timedelta

# Helper function to convert minutes since midnight to "HH:MM" string format.
def minutes_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Check if two time intervals [start1, end1) and [start2, end2) overlap.
def intervals_overlap(start1, end1, start2, end2):
    return start1 < end2 and start2 < end1

# Function to check if a meeting starting at 'start' (in minutes) for 'duration' minutes is free for a participant's schedule.
def is_free(busy_intervals, meeting_start, meeting_end):
    for interval in busy_intervals:
        busy_start, busy_end = interval
        # If the meeting overlaps with a busy interval, then it's not free.
        if intervals_overlap(meeting_start, meeting_end, busy_start, busy_end):
            return False
    return True

# Define the meeting duration in minutes
meeting_duration = 30

# Define workday boundaries (in minutes since midnight) for Monday: 9:00 (540) to 17:00 (1020)
workday_start = 9 * 60  # 540
workday_end   = 17 * 60 # 1020

# Participant schedules represented as lists of busy intervals (start, end) in minutes
# Daniel: free all day
daniel_busy = []

# Kathleen: busy during 14:30 to 15:30
kathleen_busy = [(14 * 60 + 30, 15 * 60 + 30)]  # (870,930)

# Carolyn: busy during 12:00 to 12:30 and 13:00 to 13:30
carolyn_busy = [(12 * 60, 12 * 60 + 30), (13 * 60, 13 * 60 + 30)]  # (720,750) and (780,810)

# Roger: free all day, but prefers no meeting before 12:30.
roger_busy = []  # No busy intervals; we'll enforce preference separately.
roger_preference_start = 12 * 60 + 30  # 750 minutes

# Cheryl: busy during 9:00-9:30, 10:00-11:30, 12:30-13:30, and 14:00-17:00.
cheryl_busy = [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60 + 30),
                (12 * 60 + 30, 13 * 60 + 30), (14 * 60, 17 * 60)]  # (540,570), (600,690), (750,810), (840,1020)

# Virginia: busy during 9:30-11:30, 12:00-12:30, 13:00-13:30, 14:30-15:30, and 16:00-17:00.
virginia_busy = [(9 * 60 + 30, 11 * 60 + 30), (12 * 60, 12 * 60 + 30),
                   (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 15 * 60 + 30), (16 * 60, 17 * 60)]
# (570,690), (720,750), (780,810), (870,930), (960,1020)

# Angela: busy during 9:30-10:00, 10:30-11:30, 12:00-12:30, 13:00-13:30, and 14:00-16:30.
angela_busy = [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60 + 30),
                (12 * 60, 12 * 60 + 30), (13 * 60, 13 * 60 + 30), (14 * 60, 16 * 60 + 30)]
# (570,600), (630,690), (720,750), (780,810), (840,990)

# Consolidate all busy schedules in a list for iteration.
schedules = [
    daniel_busy,
    kathleen_busy,
    carolyn_busy,
    roger_busy,   # Roger's busy is empty; his preference is handled separately.
    cheryl_busy,
    virginia_busy,
    angela_busy
]

# The meeting must be scheduled on Monday.
day_of_week = "Monday"

# We'll start checking candidate times from the maximum of workday_start and Roger's preferred start.
candidate_start = max(workday_start, roger_preference_start)
found = False
meeting_time = None

while candidate_start + meeting_duration <= workday_end:
    candidate_end = candidate_start + meeting_duration
    available_for_all = True
    
    # Check every participant's schedule.
    for busy in schedules:
        if not is_free(busy, candidate_start, candidate_end):
            available_for_all = False
            break

    if available_for_all:
        # We found a valid slot.
        meeting_time = (candidate_start, candidate_end)
        found = True
        break
    
    candidate_start += 1  # check next minute

if found:
    start_str = minutes_to_str(meeting_time[0])
    end_str = minutes_to_str(meeting_time[1])
    print(f"{day_of_week} {start_str}:{end_str}")
else:
    print("No available meeting slot found.")