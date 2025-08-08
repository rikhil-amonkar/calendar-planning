def time_to_minutes(t):
    # Converts "HH:MM" string to minutes since midnight.
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    # Converts minutes since midnight to "HH:MM" string.
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    # Returns a list of (start, end) in minutes of free time between work_start and work_end
    free = []
    current = work_start
    # Sort busy intervals by their start time.
    busy_sorted = sorted(busy_intervals, key=lambda interval: time_to_minutes(interval[0]))
    for interval in busy_sorted:
        busy_start = time_to_minutes(interval[0])
        busy_end = time_to_minutes(interval[1])
        if busy_start > current:
            free.append((current, busy_start))
        current = max(current, busy_end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    # Given two lists of intervals (each as tuple (start, end) in minutes),
    # return their intersection as a new list of intervals.
    i, j = 0, 0
    intersection = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find the intersection between intervals 
        start_int = max(start1, start2)
        end_int = min(end1, end2)
        if start_int < end_int:
            intersection.append((start_int, end_int))
        # Move to the next interval in the list that ends first.
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersection

if __name__ == "__main__":
    # Define workday start and end times.
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 60  # meeting duration in minutes

    # Busy schedules for each participant.
    busy_schedules = {
        "Olivia": [("12:30", "13:30"), ("14:30", "15:00"), ("16:30", "17:00")],
        "Anna":    [],
        "Virginia": [("9:00", "10:00"), ("11:30", "16:00"), ("16:30", "17:00")],
        "Paul":    [("9:00", "9:30"), ("11:00", "11:30"), ("13:00", "14:00"), ("14:30", "16:00"), ("16:30", "17:00")]
    }

    # Compute free time intervals for each participant.
    free_times = {}
    for person, busy in busy_schedules.items():
        free_times[person] = get_free_intervals(busy, work_start, work_end)

    # Compute common free intervals by intersecting each participant's free time.
    participants = list(busy_schedules.keys())
    common_free = free_times[participants[0]]
    for person in participants[1:]:
        common_free = intersect_intervals(common_free, free_times[person])

    # Look for a free interval that can accommodate the meeting duration.
    meeting_slot = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_slot = (start, start + meeting_duration)
            break

    # Output the result with both the time range and day of the week.
    if meeting_slot:
        start_str = minutes_to_time(meeting_slot[0])
        end_str   = minutes_to_time(meeting_slot[1])
        print(f"Monday {start_str}:{end_str}")
    else:
        print("No available meeting slot found.")