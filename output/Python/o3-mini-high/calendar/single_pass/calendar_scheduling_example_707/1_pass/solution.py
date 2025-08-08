def minutes_to_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy, work_start, work_end):
    """Given a list of busy intervals (start, end) in minutes,
    return a list of free intervals within [work_start, work_end]."""
    free = []
    current = work_start
    for interval in sorted(busy, key=lambda x: x[0]):
        if current < interval[0]:
            free.append((current, interval[0]))
        current = max(current, interval[1])
    if current < work_end:
        free.append((current, work_end))
    return free

# Meeting parameters
meeting_duration = 30  # in minutes
work_start = 9 * 60    # 09:00 in minutes: 540
work_end = 17 * 60     # 17:00 in minutes: 1020

# Participant busy schedules (times in minutes)
ryan_schedule = {
    "Monday": [
        (9 * 60 + 30, 10 * 60),     # 09:30-10:00
        (11 * 60, 12 * 60),         # 11:00-12:00
        (13 * 60, 13 * 60 + 30),    # 13:00-13:30
        (15 * 60 + 30, 16 * 60)     # 15:30-16:00
    ],
    "Tuesday": [
        (11 * 60 + 30, 12 * 60 + 30),  # 11:30-12:30
        (15 * 60 + 30, 16 * 60)         # 15:30-16:00
    ],
    "Wednesday": [
        (12 * 60, 13 * 60),         # 12:00-13:00
        (15 * 60 + 30, 16 * 60),     # 15:30-16:00
        (16 * 60 + 30, 17 * 60)      # 16:30-17:00
    ]
}

adam_schedule = {
    "Monday": [
        (9 * 60, 10 * 60 + 30),     # 09:00-10:30
        (11 * 60, 13 * 60 + 30),    # 11:00-13:30
        (14 * 60, 16 * 60),         # 14:00-16:00
        (16 * 60 + 30, 17 * 60)     # 16:30-17:00
    ],
    "Tuesday": [
        (9 * 60, 10 * 60),          # 09:00-10:00
        (10 * 60 + 30, 15 * 60 + 30),# 10:30-15:30
        (16 * 60, 17 * 60)          # 16:00-17:00
    ],
    "Wednesday": [
        (9 * 60, 9 * 60 + 30),      # 09:00-09:30
        (10 * 60, 11 * 60),         # 10:00-11:00
        (11 * 60 + 30, 14 * 60 + 30),# 11:30-14:30
        (15 * 60, 15 * 60 + 30),     # 15:00-15:30
        (16 * 60, 16 * 60 + 30)      # 16:00-16:30
    ]
}

# Additional constraints:
# 1. Ryan cannot meet on Wednesday.
# 2. Adam would like to avoid Monday meetings that start before 14:30 (14:30 = 14*60+30 = 870 minutes).
#
# Allowed days for the meeting are Monday, Tuesday, or Wednesday.
# Since Ryan is not available on Wednesday and Adam prefers not to have Monday meetings (unless after 14:30),
# we will prioritize scheduling on Tuesday if a slot exists.

# To honor the preference, we try Tuesday first, then Monday.
for day in ["Tuesday", "Monday"]:
    # Skip Wednesday because Ryan cannot meet on Wednesday.
    ryan_busy = ryan_schedule.get(day, [])
    adam_busy = adam_schedule.get(day, [])
    
    ryan_free = get_free_intervals(ryan_busy, work_start, work_end)
    adam_free = get_free_intervals(adam_busy, work_start, work_end)

    # For Monday, enforce that the meeting starts no earlier than 14:30 (870 minutes)
    if day == "Monday":
        def adjust_intervals(intervals):
            adjusted = []
            for start, end in intervals:
                if end > 870:  # There's free time past 14:30
                    adjusted.append((max(start, 870), end))
            return adjusted
        ryan_free = adjust_intervals(ryan_free)
        adam_free = adjust_intervals(adam_free)

    # Look for an intersection of free intervals between Ryan and Adam
    meeting_scheduled = False
    for r_start, r_end in ryan_free:
        for a_start, a_end in adam_free:
            # The overlapping interval:
            start = max(r_start, a_start)
            end = min(r_end, a_end)
            if end - start >= meeting_duration:
                meeting_start = start
                meeting_end = start + meeting_duration
                # Output in the format "HH:MM:HH:MM Day"
                print(f"{minutes_to_str(meeting_start)}:{minutes_to_str(meeting_end)} {day}")
                meeting_scheduled = True
                break
        if meeting_scheduled:
            break
    if meeting_scheduled:
        break