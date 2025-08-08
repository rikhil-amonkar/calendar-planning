def time_to_minutes(time_str):
    """Converts 'HH:MM' to the number of minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Converts minutes since midnight to 'HH:MM' string."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, window_start, window_end):
    """
    Given a sorted list of busy intervals [(start, end), ...] and a time window,
    returns a list of free intervals within the window.
    """
    free = []
    current = window_start
    for start, end in busy_intervals:
        # If this busy interval is completely before our current window pointer, skip it.
        if end <= current:
            continue
        # If there is a gap before the busy interval starts, record it.
        if start > current:
            free.append((current, min(start, window_end)))
        current = max(current, end)
        if current >= window_end:
            break
    if current < window_end:
        free.append((current, window_end))
    return free

def intersect_intervals(list1, list2):
    """
    Returns the intersection of two lists of intervals.
    Each list is a list of tuples (start, end) where the interval is [start, end).
    """
    i, j = 0, 0
    intersections = []
    while i < len(list1) and j < len(list2):
        a_start, a_end = list1[i]
        b_start, b_end = list2[j]
        # Find overlap between intervals
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:  # There is an overlap
            intersections.append((start, end))
        # Move to the next interval from the list that ends first.
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return intersections

def intersect_many(lists):
    """
    Compute the intersection of many lists of intervals.
    """
    if not lists:
        return []
    common = lists[0]
    for other in lists[1:]:
        common = intersect_intervals(common, other)
        if not common:
            break
    return common

if __name__ == "__main__":
    # Meeting parameters
    meeting_duration = 30  # in minutes
    day = "Monday"
    # Work hours: 09:00 to 17:00 (not used directly due to additional constraints)
    overall_start = time_to_minutes("09:00")
    overall_end = time_to_minutes("17:00")
    # Margaret’s additional constraint: no meeting before 14:30, so adjust global window start.
    global_start = max(overall_start, time_to_minutes("14:30"))
    global_end = overall_end
    global_window = (global_start, global_end)
    
    # Busy schedules for each participant in (start, end) minutes.
    # Only intervals on Monday are considered.
    shirley_busy = [
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("12:00"), time_to_minutes("12:30"))
    ]
    
    jacob_busy = [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00"))
    ]
    
    stephen_busy = [
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:00"))
    ]
    
    margaret_busy = [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("10:30"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("15:00"), time_to_minutes("15:30")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    
    mason_busy = [
        (time_to_minutes("09:00"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    
    # For each person, determine free intervals within the global window.
    # Busy intervals that occur entirely before global_start won't affect the free time.
    shirley_free = get_free_intervals(shirley_busy, global_start, global_end)
    jacob_free   = get_free_intervals(jacob_busy, global_start, global_end)
    stephen_free = get_free_intervals(stephen_busy, global_start, global_end)
    # For Margaret, even if she had free time earlier, her constraint means we only consider times starting at 14:30.
    margaret_free = get_free_intervals(margaret_busy, global_start, global_end)
    mason_free   = get_free_intervals(mason_busy, global_start, global_end)
    
    # Compute the common free intervals among all participants.
    common_free = intersect_many([shirley_free, jacob_free, stephen_free, margaret_free, mason_free])
    
    # Find the earliest interval that can hold the meeting.
    scheduled = None
    for interval_start, interval_end in common_free:
        if interval_end - interval_start >= meeting_duration:
            scheduled_start = interval_start
            scheduled_end = scheduled_start + meeting_duration
            scheduled = (scheduled_start, scheduled_end)
            break
    
    if scheduled:
        start_str = minutes_to_time(scheduled[0])
        end_str = minutes_to_time(scheduled[1])
        # Output format: HH:MM:HH:MM with the day appended.
        print(f"{day} {start_str}:{end_str}")
    else:
        print("No available time slot found.")