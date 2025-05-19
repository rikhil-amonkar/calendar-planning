# Meeting scheduling script for Eric and Henry on Monday
# Meeting duration is 30 minutes and meeting must be before 10:00 because Henry prefers to avoid meetings after 10:00.
# Eric's blocked times: 12:00-13:00 and 14:00-15:00.
# Henry's meetings: 
#   09:30-10:00, 10:30-11:00, 11:30-12:30, 13:00-13:30, 14:30-15:00, 16:00-17:00.
# Since Henry prefers not to meet after 10:00,
# a natural candidate is 09:00 to 09:30 on Monday, which works for both.

from datetime import datetime, timedelta

def minutes_since_start(time_str):
    # convert "HH:MM" to minutes since 00:00
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def format_time(minutes):
    # Format minutes since midnight back to "HH:MM"
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Define working day boundaries (9:00 to 17:00)
work_start = minutes_since_start("09:00")
work_end = minutes_since_start("17:00")

# Blocked intervals for Eric and Henry for Monday (in minutes)
eric_blocks = [
    (minutes_since_start("12:00"), minutes_since_start("13:00")),
    (minutes_since_start("14:00"), minutes_since_start("15:00"))
]

henry_blocks = [
    (minutes_since_start("09:30"), minutes_since_start("10:00")),
    (minutes_since_start("10:30"), minutes_since_start("11:00")),
    (minutes_since_start("11:30"), minutes_since_start("12:30")),
    (minutes_since_start("13:00"), minutes_since_start("13:30")),
    (minutes_since_start("14:30"), minutes_since_start("15:00")),
    (minutes_since_start("16:00"), minutes_since_start("17:00"))
]

# Henry's preference: no meetings after 10:00 on Monday.
henry_latest = minutes_since_start("10:00")

# Meeting duration in minutes
meeting_duration = 30

# We must choose a start time such that the meeting finishes by min(work_end, henry_latest)
# because of the preference for Henry.
latest_possible_end = min(work_end, henry_latest)  # meeting must end by 10:00
latest_possible_start = latest_possible_end - meeting_duration

candidate = None

# We'll try time slots starting from work_start (9:00) till latest_possible_start
for start in range(work_start, latest_possible_start + 1):
    end = start + meeting_duration
    
    # Check if this time slot is conflict free for Eric and Henry
    conflict = False
    
    # Check Eric's blocks
    for eb_start, eb_end in eric_blocks:
        if not (end <= eb_start or start >= eb_end):
            conflict = True
            break
    if conflict:
        continue
    
    # Check Henry's blocks
    for hb_start, hb_end in henry_blocks:
        if not (end <= hb_start or start >= hb_end):
            conflict = True
            break
    if conflict:
        continue
    
    # Candidate slot should also end by henry_latest
    if end > henry_latest:
        continue
    
    candidate = (start, end)
    break

if candidate:
    start_time = format_time(candidate[0])
    end_time = format_time(candidate[1])
    day = "Monday"
    print(f"{day} {start_time}:{end_time}")
else:
    print("No suitable time block found.")