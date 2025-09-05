def minutes_to_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def find_free_slot(busy_intervals, work_start, work_end, duration):
    # Ensure the busy intervals are sorted by start time.
    busy_intervals = sorted(busy_intervals, key=lambda x: x[0])
    current = work_start
    for start, end in busy_intervals:
        if current + duration <= start:
            return current
        # If the current time falls into a busy interval, move to its end.
        if current < end:
            current = end
    # Check if there is enough time between the last busy interval and work_end.
    if current + duration <= work_end:
        return current
    return None

# Working hours (in minutes from midnight)
work_start = 9 * 60   # 09:00
work_end = 17 * 60    # 17:00
meeting_duration = 60  # 1 hour meeting

# Busy schedule for Roy (Patrick is free all week)
# Each busy slot is represented as a tuple (start_in_minutes, end_in_minutes)
schedules = {
    "Monday": [
        (10 * 60, 11 * 60 + 30),  # 10:00 - 11:30
        (12 * 60, 13 * 60),       # 12:00 - 13:00
        (14 * 60, 14 * 60 + 30),  # 14:00 - 14:30
        (15 * 60, 17 * 60)        # 15:00 - 17:00
    ],
    "Tuesday": [
        (10 * 60 + 30, 11 * 60 + 30),  # 10:30 - 11:30
        (12 * 60, 14 * 60 + 30),         # 12:00 - 14:30
        (15 * 60, 15 * 60 + 30),         # 15:00 - 15:30
        (16 * 60, 17 * 60)               # 16:00 - 17:00
    ],
    "Wednesday": [
        (9 * 60 + 30, 11 * 60 + 30),  # 09:30 - 11:30
        (12 * 60 + 30, 14 * 60),      # 12:30 - 14:00
        (14 * 60 + 30, 15 * 60 + 30), # 14:30 - 15:30
        (16 * 60 + 30, 17 * 60)       # 16:30 - 17:00
    ]
}

# Check days in order for the earliest available meeting slot.
for day in ["Monday", "Tuesday", "Wednesday"]:
    free_start = find_free_slot(schedules[day], work_start, work_end, meeting_duration)
    if free_start is not None:
        start_str = minutes_to_str(free_start)
        end_str = minutes_to_str(free_start + meeting_duration)
        # Output format: Day: HH:MM:HH:MM
        print(f"{day}: {start_str}:{end_str}")
        break