def time_to_minutes(t):
    """Convert HH:MM string to minutes from midnight."""
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes from midnight to HH:MM string."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy, work_start, work_end):
    """
    Given a list of busy intervals [(start, end), ...] as HH:MM strings,
    return a list of free intervals in minutes between work_start and work_end.
    """
    # Convert busy intervals to minutes and sort them.
    busy_minutes = sorted([(time_to_minutes(s), time_to_minutes(e)) for s, e in busy])
    free = []
    current = work_start
    for start, end in busy_minutes:
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """
    Compute the intersection of two lists of intervals.
    Each interval is a tuple (start, end) in minutes.
    """
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        a1, b1 = intervals1[i]
        a2, b2 = intervals2[j]
        start = max(a1, a2)
        end = min(b1, b2)
        if start < end:
            intersections.append((start, end))
        if b1 < b2:
            i += 1
        else:
            j += 1
    return intersections

def main():
    meeting_duration = 30  # minutes
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    
    # Schedules for Monday, Tuesday, and Wednesday.
    schedules = {
        "Monday": {
            "Ryan": [
                ("09:30", "10:00"),
                ("11:00", "12:00"),
                ("13:00", "13:30"),
                ("15:30", "16:00")
            ],
            "Adam": [
                ("09:00", "10:30"),
                ("11:00", "13:30"),
                ("14:00", "16:00"),
                ("16:30", "17:00")
            ]
        },
        "Tuesday": {
            "Ryan": [
                ("11:30", "12:30"),
                ("15:30", "16:00")
            ],
            "Adam": [
                ("09:00", "10:00"),
                ("10:30", "15:30"),
                ("16:00", "17:00")
            ]
        },
        "Wednesday": {
            "Ryan": [
                ("12:00", "13:00"),
                ("15:30", "16:00"),
                ("16:30", "17:00")
            ],
            "Adam": [
                ("09:00", "09:30"),
                ("10:00", "11:00"),
                ("11:30", "14:30"),
                ("15:00", "15:30"),
                ("16:00", "16:30")
            ]
        }
    }
    
    # According to the constraints:
    # Ryan cannot meet on Wednesday.
    # Adam would like to avoid additional Monday meetings before 14:30.
    # We'll prioritize Tuesday if a slot exists.
    candidate_days = ["Tuesday", "Monday"]
    
    for day in candidate_days:
        # Skip Wednesday since Ryan is not available.
        if day == "Wednesday":
            continue
        
        busy_ryan = schedules.get(day, {}).get("Ryan", [])
        busy_adam = schedules.get(day, {}).get("Adam", [])
        
        # Compute free intervals for each participant within work hours.
        free_ryan = get_free_intervals(busy_ryan, work_start, work_end)
        free_adam = get_free_intervals(busy_adam, work_start, work_end)
        
        # Find intersection of free intervals.
        common_free = intersect_intervals(free_ryan, free_adam)
        
        for interval in common_free:
            interval_start, interval_end = interval
            # For Monday, respect Adam's preference: avoid meetings before 14:30.
            if day == "Monday":
                candidate_start = max(interval_start, time_to_minutes("14:30"))
            else:
                candidate_start = interval_start
            # Check if there's enough time in this interval.
            if candidate_start + meeting_duration <= interval_end:
                meeting_start = candidate_start
                meeting_end = candidate_start + meeting_duration
                start_str = minutes_to_time(meeting_start)
                end_str = minutes_to_time(meeting_end)
                # Output: Day and meeting time in HH:MM:HH:MM format.
                print(f"{day} {{{start_str}:{end_str}}}")
                return

    print("No available meeting slot found.")

if __name__ == "__main__":
    main()