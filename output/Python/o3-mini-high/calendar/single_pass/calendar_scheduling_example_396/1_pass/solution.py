def minutes_to_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def is_free(meeting_start, meeting_end, busy_times):
    # Check if the [meeting_start, meeting_end) interval overlaps any busy interval.
    for bs, be in busy_times:
        if meeting_start < be and bs < meeting_end:
            return False
    return True

# Define working hours (in minutes from midnight)
work_start = 9 * 60    # 9:00  -> 540
work_end   = 17 * 60   # 17:00 -> 1020
duration = 30          # meeting duration in minutes

# Busy schedules for participants (times in minutes)
busy = {
    "Andrea": [],
    "Jack": [(540, 570), (840, 870)],              # 9:00-9:30, 14:00-14:30
    "Madison": [(570, 630), (780, 840), (900, 930), (990, 1020)],  # 9:30-10:30, 13:00-14:00, 15:00-15:30, 16:30-17:00
    "Rachel": [(570, 630), (660, 690), (720, 810), (870, 930), (960, 1020)],  # 9:30-10:30, 11:00-11:30, 12:00-13:30, 14:30-15:30, 16:00-17:00
    "Douglas": [(540, 690), (720, 990)],             # 9:00-11:30, 12:00-16:30
    "Ryan": [(540, 570), (780, 840), (870, 1020)]      # 9:00-9:30, 13:00-14:00, 14:30-17:00
}

meeting_time = None

# Iterate over possible start times (minute by minute)
for start in range(work_start, work_end - duration + 1):
    end = start + duration
    # Check for each person if the meeting slot is free.
    if all(is_free(start, end, busy[person]) for person in busy):
        meeting_time = (start, end)
        break

if meeting_time:
    meeting_start_str = minutes_to_str(meeting_time[0])
    meeting_end_str = minutes_to_str(meeting_time[1])
    # The day is Monday and the requested output format is HH:MM:HH:MM with the day.
    print(f"Monday {meeting_start_str}:{meeting_end_str}")
else:
    print("No available meeting time found.")