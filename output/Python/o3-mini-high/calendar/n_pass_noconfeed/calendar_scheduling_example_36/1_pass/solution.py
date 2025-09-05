def minutes_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(start, end, busy_intervals):
    """Return free intervals within [start, end] given a sorted list of busy intervals."""
    free = []
    current = start
    for b_start, b_end in busy_intervals:
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < end:
        free.append((current, end))
    return free

def intersect_two(interval1, interval2):
    """Return the intersection of two intervals if it exists, otherwise None."""
    new_start = max(interval1[0], interval2[0])
    new_end = min(interval1[1], interval2[1])
    if new_start < new_end:
        return (new_start, new_end)
    return None

def intersect_intervals(list1, list2):
    """Intersect two lists of intervals and return the overlapping intervals."""
    result = []
    for int1 in list1:
        for int2 in list2:
            inter = intersect_two(int1, int2)
            if inter is not None:
                result.append(inter)
    return result

def filter_by_window(intervals, window):
    """Intersect each interval with a given window."""
    windowed = []
    for interval in intervals:
        inter = intersect_two(interval, window)
        if inter is not None:
            windowed.append(inter)
    return windowed

def filter_by_duration(intervals, duration):
    """Return intervals that can accommodate the meeting duration."""
    return [interval for interval in intervals if interval[1] - interval[0] >= duration]

def main():
    # Meeting parameters
    meeting_duration = 60  # in minutes
    meeting_day = "Monday"
    
    # Work hours in minutes (9:00 to 17:00)
    work_start = 9 * 60    # 09:00 -> 540 minutes
    work_end = 17 * 60     # 17:00 -> 1020 minutes
    
    # Denise's constraint: Do not want to meet on Monday after 12:30.
    # So the meeting must end by 12:30 (i.e., 750 minutes).
    constraint_end = 12 * 60 + 30  # 12:30 -> 750 minutes
    
    # The overall scheduling window is the work hours up to the constraint end.
    scheduling_window = (work_start, constraint_end)
    
    # Busy schedules for each participant (in minutes)
    # Ryan is busy: 9:00 - 9:30 and 12:30 - 13:00.
    ryan_busy = [
        (9 * 60, 9 * 60 + 30),       # 09:00 - 09:30
        (12 * 60 + 30, 13 * 60)      # 12:30 - 13:00
    ]
    
    # Ruth has no meetings.
    ruth_busy = []
    
    # Denise is busy: 9:30 - 10:30, 12:00 - 13:00, 14:30 - 16:30.
    denise_busy = [
        (9 * 60 + 30, 10 * 60 + 30),  # 09:30 - 10:30
        (12 * 60, 13 * 60),           # 12:00 - 13:00
        (14 * 60 + 30, 16 * 60 + 30)  # 14:30 - 16:30
    ]
    
    # Compute free intervals during work hours for each participant.
    ryan_free = get_free_intervals(work_start, work_end, ryan_busy)
    ruth_free = get_free_intervals(work_start, work_end, ruth_busy)
    denise_free = get_free_intervals(work_start, work_end, denise_busy)
    
    # Restrict free intervals to the scheduling window (i.e. before or at 12:30).
    ryan_free = filter_by_window(ryan_free, scheduling_window)
    ruth_free = filter_by_window(ruth_free, scheduling_window)
    denise_free = filter_by_window(denise_free, scheduling_window)
    
    # Find common free intervals among all participants.
    common_free = intersect_intervals(ryan_free, ruth_free)
    common_free = intersect_intervals(common_free, denise_free)
    
    # Filter the intervals that can accommodate the meeting duration.
    available = filter_by_duration(common_free, meeting_duration)
    
    if available:
        # Pick the earliest available interval.
        meeting_start = min(available, key=lambda interval: interval[0])[0]
        meeting_end = meeting_start + meeting_duration
        
        start_str = minutes_to_str(meeting_start)
        end_str = minutes_to_str(meeting_end)
        print(f"{meeting_day} {start_str}:{end_str}")
    else:
        print("No available time slot found.")

if __name__ == "__main__":
    main()