def time_to_minutes(t):
    """Converts a time string "HH:MM" to minutes since midnight."""
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Converts minutes since midnight to time string "HH:MM"."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy, work_start, work_end):
    """Given a list of busy intervals (each as (start, end) strings),
    returns a list of free intervals (in minutes) between work_start and work_end.
    Assumes busy intervals do not overlap."""
    busy_sorted = sorted(busy, key=lambda interval: time_to_minutes(interval[0]))
    free = []
    current = work_start
    for b in busy_sorted:
        b_start = time_to_minutes(b[0])
        b_end = time_to_minutes(b[1])
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """Intersects two lists of intervals (each interval is a tuple (start, end) in minutes).
    Returns the list of intersecting intervals."""
    i, j = 0, 0
    intersection = []
    while i < len(intervals1) and j < len(intervals2):
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if start < end:
            intersection.append((start, end))
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return intersection

def main():
    # Define work hours (in minutes since midnight)
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 30  # in minutes

    # Define each participant's busy intervals on Monday
    schedules = {
        "Joan": [("11:30", "12:00"), ("14:30", "15:00")],
        "Megan": [("09:00", "10:00"), ("14:00", "14:30"), ("16:00", "16:30")],
        "Austin": [],  # free entire day
        "Betty": [("09:30", "10:00"), ("11:30", "12:00"), ("13:30", "14:00"), ("16:00", "16:30")],
        "Judith": [("09:00", "11:00"), ("12:00", "13:00"), ("14:00", "15:00")],
        "Terry": [("09:30", "10:00"), ("11:30", "12:30"), ("13:00", "14:00"), ("15:00", "15:30"), ("16:00", "17:00")],
        "Kathryn": [("09:30", "10:00"), ("10:30", "11:00"), ("11:30", "13:00"), ("14:00", "16:00"), ("16:30", "17:00")]
    }
    
    # Compute free intervals for each participant
    free_times = {}
    for person, busy in schedules.items():
        free_times[person] = get_free_intervals(busy, work_start, work_end)
    
    # Compute the common free intervals across all participants.
    # Start with one participant's free intervals.
    all_free = list(free_times[next(iter(schedules))])
    for person in schedules:
        all_free = intersect_intervals(all_free, free_times[person])
    
    # Find the first common free interval that can accommodate the meeting.
    meeting_slot = None
    for interval in all_free:
        if interval[1] - interval[0] >= meeting_duration:
            meeting_slot = (interval[0], interval[0] + meeting_duration)
            break

    # Output in the format "HH:MM:HH:MM" along with the day of the week.
    if meeting_slot:
        start_time = minutes_to_time(meeting_slot[0])
        end_time = minutes_to_time(meeting_slot[1])
        day = "Monday"
        print(f"{day} {start_time}:{end_time}")
    else:
        print("No available slot found.")

if __name__ == "__main__":
    main()