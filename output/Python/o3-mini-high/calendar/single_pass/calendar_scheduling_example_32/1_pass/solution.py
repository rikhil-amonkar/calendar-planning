def time_to_minutes(time_str):
    """Convert a time string in HH:MM format to the number of minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight back into a HH:MM formatted string."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02}:{mins:02}"

def get_free_intervals(busy, work_start, work_end):
    """
    Given a sorted list of busy intervals (as (start, end) in minutes) and overall working hours,
    return a list of free intervals (as (start, end) in minutes).
    """
    free = []
    current = work_start
    for start_busy, end_busy in busy:
        if start_busy > current:
            free.append((current, start_busy))
        current = max(current, end_busy)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(list1, list2):
    """
    Given two lists of intervals, return their intersection.
    Each interval is a tuple (start, end) in minutes.
    """
    i, j = 0, 0
    result = []
    while i < len(list1) and j < len(list2):
        # Find the intersection between list1[i] and list2[j]
        start = max(list1[i][0], list2[j][0])
        end = min(list1[i][1], list2[j][1])
        if start < end:
            result.append((start, end))
        # Advance the pointer that ends first
        if list1[i][1] < list2[j][1]:
            i += 1
        else:
            j += 1
    return result

def main():
    # Define working hours: 9:00 to 17:00
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 30  # minutes

    # Busy intervals for each participant on Monday (in HH:MM converted to minutes)
    # Emily's busy intervals
    emily_busy = [
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:30"), time_to_minutes("12:30")),
        (time_to_minutes("14:00"), time_to_minutes("15:00")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ]
    
    # Melissa's busy intervals
    melissa_busy = [
        (time_to_minutes("09:30"), time_to_minutes("10:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00"))
    ]
    
    # Frank's busy intervals
    frank_busy = [
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("13:30"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]

    # Compute free intervals during work hours for each participant
    emily_free = get_free_intervals(emily_busy, work_start, work_end)
    melissa_free = get_free_intervals(melissa_busy, work_start, work_end)
    frank_free = get_free_intervals(frank_busy, work_start, work_end)
    
    # Apply Frank's constraint: He does not want to meet on Monday after 9:30.
    # Restrict his available time to before 9:30.
    constraint_interval = [(work_start, time_to_minutes("09:30"))]
    frank_free = intersect_intervals(frank_free, constraint_interval)
    
    # Find common free intervals among Emily and Melissa
    common_free = intersect_intervals(emily_free, melissa_free)
    # Intersect with Frank's (constrained) free intervals
    common_free = intersect_intervals(common_free, frank_free)
    
    # Look for a free interval that can accommodate the meeting duration
    meeting_slot = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_slot = (start, start + meeting_duration)
            break

    if meeting_slot:
        start_time = minutes_to_time(meeting_slot[0])
        end_time = minutes_to_time(meeting_slot[1])
        # Output the meeting time and day in the format: HH:MM:HH:MM (with day)
        print(f"Monday {start_time}:{end_time}")
    else:
        print("No available meeting slot found.")

if __name__ == "__main__":
    main()