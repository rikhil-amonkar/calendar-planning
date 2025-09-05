def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def invert_busy_intervals(busy, work_start, work_end):
    """Given a list of busy intervals (start, end) in minutes,
    return a list of free intervals within [work_start, work_end]."""
    free = []
    current = work_start
    # Sort the busy intervals by their start time.
    for b_start, b_end in sorted(busy, key=lambda x: x[0]):
        if current < b_start:
            free.append((current, b_start))
        # Move the current time pointer forward.
        if current < b_end:
            current = b_end
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """Find the intersection between two lists of intervals."""
    intersection = []
    for start1, end1 in intervals1:
        for start2, end2 in intervals2:
            start = max(start1, start2)
            end = min(end1, end2)
            if start < end:
                intersection.append((start, end))
    return intersection

def main():
    # Define work day in minutes: 9:00 to 17:00
    work_start = 9 * 60      # 540 minutes = 9:00
    work_end = 17 * 60       # 1020 minutes = 17:00
    meeting_duration = 30    # meeting duration in minutes

    # Busy schedules for each participant (in minutes)
    schedules = {
        "Tyler": [],
        "Kelly": [],
        "Stephanie": [
            (11 * 60, 11 * 60 + 30),       # 11:00 - 11:30
            (14 * 60 + 30, 15 * 60)        # 14:30 - 15:00
        ],
        "Hannah": [],
        "Joe": [
            (9 * 60, 9 * 60 + 30),         # 9:00 - 9:30
            (10 * 60, 12 * 60),            # 10:00 - 12:00
            (12 * 60 + 30, 13 * 60),       # 12:30 - 13:00
            (14 * 60, 17 * 60)             # 14:00 - 17:00
        ],
        "Diana": [
            (9 * 60, 10 * 60 + 30),        # 9:00 - 10:30
            (11 * 60 + 30, 12 * 60),       # 11:30 - 12:00
            (13 * 60, 14 * 60),            # 13:00 - 14:00
            (14 * 60 + 30, 15 * 60 + 30),  # 14:30 - 15:30
            (16 * 60, 17 * 60)             # 16:00 - 17:00
        ],
        "Deborah": [
            (9 * 60, 10 * 60),             # 9:00 - 10:00
            (10 * 60 + 30, 12 * 60),       # 10:30 - 12:00
            (12 * 60 + 30, 13 * 60),       # 12:30 - 13:00
            (13 * 60 + 30, 14 * 60),       # 13:30 - 14:00
            (14 * 60 + 30, 15 * 60 + 30),  # 14:30 - 15:30
            (16 * 60, 16 * 60 + 30)        # 16:00 - 16:30
        ]
    }

    # Start with full work day as common free interval.
    common_free = [(work_start, work_end)]
    
    # For each participant, compute their free intervals and intersect them.
    for person, busy in schedules.items():
        free = invert_busy_intervals(busy, work_start, work_end)
        common_free = intersect_intervals(common_free, free)

    # Find the earliest common free interval where a meeting can fit.
    meeting_slot = None
    for start, end in sorted(common_free):
        if end - start >= meeting_duration:
            meeting_slot = (start, start + meeting_duration)
            break

    if meeting_slot:
        start_str = minutes_to_time(meeting_slot[0])
        end_str = minutes_to_time(meeting_slot[1])
        day = "Monday"
        # Output in format: "Day HH:MM:HH:MM"
        print(f"{day} {start_str}:{end_str}")
    else:
        print("No available meeting time found.")

if __name__ == "__main__":
    main()