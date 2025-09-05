def get_free_intervals(busy, work_start, work_end):
    """Return list of free intervals given busy intervals and working hours."""
    free = []
    busy_sorted = sorted(busy, key=lambda x: x[0])
    current = work_start

    for interval in busy_sorted:
        busy_start, busy_end = interval
        if busy_start > current:
            free.append((current, busy_start))
        current = max(current, busy_end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """Return the intersection of two lists of intervals."""
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find overlap:
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            intersections.append((start_overlap, end_overlap))
        # Move to the next interval in the list that ends first.
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

def minutes_to_str(minutes):
    """Convert minutes since midnight to HH:MM string."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    # Define work hours for Monday: 9:00 (540 mins) to 17:00 (1020 mins)
    work_start = 9 * 60
    work_end = 17 * 60

    # Meeting duration in minutes
    meeting_duration = 30

    # Define busy intervals in minutes for Adam and Roy.
    # Each tuple is (start, end) in minutes since midnight.
    adams_busy = [
        (9 * 60 + 30, 10 * 60),     # 09:30 - 10:00
        (12 * 60 + 30, 13 * 60),    # 12:30 - 13:00
        (14 * 60 + 30, 15 * 60),    # 14:30 - 15:00
        (16 * 60 + 30, 17 * 60)     # 16:30 - 17:00
    ]

    roys_busy = [
        (10 * 60, 11 * 60),         # 10:00 - 11:00
        (11 * 60 + 30, 13 * 60),    # 11:30 - 13:00
        (13 * 60 + 30, 14 * 60 + 30),  # 13:30 - 14:30
        (16 * 60 + 30, 17 * 60)     # 16:30 - 17:00
    ]

    # Calculate free intervals for both participants.
    adams_free = get_free_intervals(adams_busy, work_start, work_end)
    roys_free = get_free_intervals(roys_busy, work_start, work_end)

    # Find common free intervals.
    common_free = intersect_intervals(adams_free, roys_free)

    # Find the earliest interval that fits the meeting duration.
    meeting_time = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_time = (start, start + meeting_duration)
            break

    # Output the meeting time in the format "HH:MM:HH:MM" with the day.
    if meeting_time:
        start_time, end_time = meeting_time
        print(f"Monday {minutes_to_str(start_time)}:{minutes_to_str(end_time)}")
    else:
        print("No available slot found.")

if __name__ == "__main__":
    main()