def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy, work_start, work_end):
    # Assumes busy intervals are tuples (start, end) in minutes and sorted by start time.
    free = []
    current = work_start
    for b_start, b_end in sorted(busy):
        if current < b_start:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    intersections = []
    for start1, end1 in intervals1:
        for start2, end2 in intervals2:
            start_int = max(start1, start2)
            end_int = min(end1, end2)
            if start_int < end_int:
                intersections.append((start_int, end_int))
    return intersections

# Meeting and work settings
meeting_duration = 60  # minutes
work_start = 9 * 60    # 9:00 AM in minutes
work_end = 17 * 60     # 17:00 in minutes

# Busy schedules in minutes for each participant by day

# Monday busy intervals (in minutes)
gary_busy = {
    "Monday": [
        (9 * 60 + 30, 10 * 60),   # 09:30 - 10:00
        (11 * 60, 13 * 60),        # 11:00 - 13:00
        (14 * 60, 14 * 60 + 30),   # 14:00 - 14:30
        (16 * 60 + 30, 17 * 60)    # 16:30 - 17:00
    ],
    "Tuesday": [
        (9 * 60, 9 * 60 + 30),     # 09:00 - 09:30
        (10 * 60 + 30, 11 * 60),   # 10:30 - 11:00
        (14 * 60 + 30, 16 * 60)    # 14:30 - 16:00
    ]
}

david_busy = {
    "Monday": [
        (9 * 60, 9 * 60 + 30),     # 09:00 - 09:30
        (10 * 60, 13 * 60),        # 10:00 - 13:00
        (14 * 60 + 30, 16 * 60 + 30)  # 14:30 - 16:30
    ],
    "Tuesday": [
        (9 * 60, 9 * 60 + 30),     # 09:00 - 09:30
        (10 * 60, 10 * 60 + 30),   # 10:00 - 10:30
        (11 * 60, 12 * 60 + 30),   # 11:00 - 12:30
        (13 * 60, 14 * 60 + 30),   # 13:00 - 14:30
        (15 * 60, 16 * 60),        # 15:00 - 16:00
        (16 * 60 + 30, 17 * 60)    # 16:30 - 17:00
    ]
}

# Try scheduling on Monday or Tuesday
for day in ["Monday", "Tuesday"]:
    # Compute free intervals for both participants
    free_gary = get_free_intervals(gary_busy[day], work_start, work_end)
    free_david = get_free_intervals(david_busy[day], work_start, work_end)
    
    # Find overlapping free intervals
    common_free = intersect_intervals(free_gary, free_david)
    
    # Look for an interval that can accommodate the meeting duration
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = meeting_start + meeting_duration
            meeting_time_str = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
            print(f"Proposed meeting time: {day} {meeting_time_str}")
            exit(0)

print("No available meeting slot found.")