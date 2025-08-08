def time_to_minutes(time_str):
    """Convert HH:MM string to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to HH:MM string."""
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    """
    Given a sorted list of busy intervals (tuples of start and end in minutes)
    and the overall working period, return a list of free intervals.
    """
    free = []
    current = work_start
    for start, end in sorted(busy_intervals):
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """
    Intersect two lists of intervals and return the overlapping intervals.
    Both input lists must be sorted.
    """
    res = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        a_start, a_end = intervals1[i]
        b_start, b_end = intervals2[j]
        # Find the overlap between the two intervals.
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            res.append((start, end))
        # Advance the list that finishes first.
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return res

def find_meeting_slot(common_free, duration):
    """
    Finds the first free interval that can accommodate the meeting duration.
    Returns a tuple (start, end) in minutes or None if no slot is found.
    """
    for start, end in common_free:
        if end - start >= duration:
            return start, start + duration
    return None

def main():
    # Define working hours and meeting duration in minutes
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 30  # in minutes
    day = "Monday"
    
    # Define each participant's busy intervals (in HH:MM)
    busy_jacob = [
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00"))
    ]
    busy_diana = [
        (time_to_minutes("09:30"), time_to_minutes("10:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ]
    busy_adam = [
        (time_to_minutes("09:30"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("12:30")),
        (time_to_minutes("15:30"), time_to_minutes("16:00"))
    ]
    busy_angela = [
        (time_to_minutes("09:30"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("12:00")),
        (time_to_minutes("13:00"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ]
    busy_dennis = [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("10:30"), time_to_minutes("11:30")),
        (time_to_minutes("13:00"), time_to_minutes("15:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    
    # Compute free intervals for each participant within working hours
    free_jacob = get_free_intervals(busy_jacob, work_start, work_end)
    free_diana = get_free_intervals(busy_diana, work_start, work_end)
    free_adam = get_free_intervals(busy_adam, work_start, work_end)
    free_angela = get_free_intervals(busy_angela, work_start, work_end)
    free_dennis = get_free_intervals(busy_dennis, work_start, work_end)
    
    # Compute common free intervals (start with one participant and intersect iteratively)
    common_free = free_jacob
    for free in [free_diana, free_adam, free_angela, free_dennis]:
        common_free = intersect_intervals(common_free, free)
    
    # Find a free slot that can accommodate the meeting duration
    slot = find_meeting_slot(common_free, meeting_duration)
    if slot:
        start, end = slot
        # Output in the required format: HH:MM:HH:MM and the day of the week.
        print(f"{minutes_to_time(start)}:{minutes_to_time(end)} {day}")
    else:
        print("No suitable meeting slot found.")

if __name__ == "__main__":
    main()