def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def compute_free_intervals(busy, start, end):
    """Given a list of busy intervals (tuples of start and end in minutes),
    compute and return a list of free intervals within [start, end]."""
    free = []
    current = start
    for b_start, b_end in sorted(busy):
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < end:
        free.append((current, end))
    return free

# Define working hours in minutes (9:00 to 17:00)
WORK_START = 9 * 60      # 540
WORK_END   = 17 * 60     # 1020
MEETING_DURATION = 30    # in minutes

# John's schedule is completely free, but he prefers to avoid
# meetings on Monday after 14:30 (which is 14*60 + 30 = 870 minutes).
MONDAY_LIMIT = 14 * 60 + 30  # 870

# Jennifer's meetings (in minutes) on each day.
schedules = {
    "Monday": [
        (9 * 60, 11 * 60),           # 09:00-11:00
        (11 * 60 + 30, 13 * 60),      # 11:30-13:00
        (13 * 60 + 30, 14 * 60 + 30), # 13:30-14:30
        (15 * 60, 17 * 60)            # 15:00-17:00
    ],
    "Tuesday": [
        (9 * 60, 11 * 60 + 30),       # 09:00-11:30
        (12 * 60, 17 * 60)            # 12:00-17:00
    ],
    "Wednesday": [
        (9 * 60, 11 * 60 + 30),       # 09:00-11:30
        (12 * 60, 12 * 60 + 30),      # 12:00-12:30
        (13 * 60, 14 * 60),           # 13:00-14:00
        (14 * 60 + 30, 16 * 60),      # 14:30-16:00
        (16 * 60 + 30, 17 * 60)       # 16:30-17:00
    ]
}

# Preferred days order
for day in ["Monday", "Tuesday", "Wednesday"]:
    # For Monday, John's constraint forces the meeting to end by 14:30.
    if day == "Monday":
        day_end_limit = MONDAY_LIMIT
    else:
        day_end_limit = WORK_END

    # Compute free intervals for Jennifer from WORK_START to WORK_END.
    free_intervals = compute_free_intervals(schedules.get(day, []), WORK_START, WORK_END)
    
    # If Monday, we only consider free slots that end no later than 14:30.
    for interval in free_intervals:
        free_start, free_end = interval
        if day == "Monday":
            free_end = min(free_end, day_end_limit)
        if free_end - free_start >= MEETING_DURATION:
            meeting_start = free_start
            meeting_end = meeting_start + MEETING_DURATION
            start_str = minutes_to_time(meeting_start)
            end_str = minutes_to_time(meeting_end)
            # Output in the format HH:MM:HH:MM along with the day of the week.
            print(f"{start_str}:{end_str} on {day}")
            exit(0)

# In case no slot is found (although the problem guarantees one)
print("No available time slot found.")