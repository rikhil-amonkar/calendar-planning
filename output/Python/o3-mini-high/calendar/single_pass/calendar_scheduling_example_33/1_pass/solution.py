def minutes_to_time(minutes):
    """Convert minutes since midnight into HH:MM format."""
    hr = minutes // 60
    mn = minutes % 60
    return f"{hr:02d}:{mn:02d}"

def get_free_intervals(busy, window_start, window_end):
    """
    Given a list of busy intervals (each as a tuple (start, end) in minutes)
    and an overall window [window_start, window_end], return a list of free intervals.
    Assumes busy intervals are non-overlapping and sorted by start time.
    """
    free = []
    current = window_start
    for b_start, b_end in sorted(busy):
        # If the busy interval ends before the window starts or starts after window end, skip it.
        if b_end <= window_start or b_start >= window_end:
            continue
        # Clip busy interval to the window boundaries.
        b_start_clipped = max(b_start, window_start)
        b_end_clipped = min(b_end, window_end)
        if current < b_start_clipped:
            free.append((current, b_start_clipped))
        current = max(current, b_end_clipped)
    if current < window_end:
        free.append((current, window_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """
    Given two lists of intervals, return their intersection as a list of intervals.
    Each interval is a tuple (start, end) with start and end in minutes.
    """
    i, j = 0, 0
    intersection = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find overlap
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            intersection.append((start_overlap, end_overlap))
        # Move to the next interval in the list which ends first.
        if end1 <= end2:
            i += 1
        else:
            j += 1
    return intersection

def find_meeting_slot(common_free, duration):
    """
    From a list of common free intervals, find the earliest slot
    that can accommodate a meeting of 'duration' minutes.
    """
    for start, end in common_free:
        if end - start >= duration:
            return start, start + duration
    return None

def main():
    # Meeting parameters
    meeting_duration = 30  # minutes
    # Work day is 9:00 to 17:00, but Bobby prefers meetings to finish by 15:00.
    # So for scheduling, we restrict the window to 9:00 to 15:00.
    window_start = 9 * 60       # 9:00 -> 540 minutes
    window_end = 15 * 60        # 15:00 -> 900 minutes

    # Busy schedules for each participant, times are in minutes since midnight.
    # Lisa's meetings on Monday: 9:00-10:00, 10:30-11:30, 12:30-13:00, 16:00-16:30.
    # Only include meetings that fall into our scheduling window [9:00, 15:00].
    lisa_busy = [
        (9 * 60, 10 * 60),         # 9:00 to 10:00 -> (540, 600)
        (10 * 60 + 30, 11 * 60 + 30),  # 10:30 to 11:30 -> (630, 690)
        (12 * 60 + 30, 13 * 60)       # 12:30 to 13:00 -> (750, 780)
        # The 16:00-16:30 meeting is outside our window.
    ]

    # Bobby's meetings on Monday: 9:00-9:30, 10:00-10:30, 11:30-12:00, 15:00-15:30.
    # Only include those in the scheduling window.
    bobby_busy = [
        (9 * 60, 9 * 60 + 30),      # 9:00 to 9:30 -> (540, 570)
        (10 * 60, 10 * 60 + 30),    # 10:00 to 10:30 -> (600, 630)
        (11 * 60 + 30, 12 * 60)     # 11:30 to 12:00 -> (690, 720)
        # 15:00-15:30 falls at the boundary so we exclude it, since the meeting must end by 15:00.
    ]

    # Randy's meetings on Monday: 9:30-10:00, 10:30-11:00, 11:30-12:30, 13:00-13:30, 14:30-15:30, 16:00-16:30.
    randy_busy = [
        (9 * 60 + 30, 10 * 60),         # 9:30 to 10:00 -> (570, 600)
        (10 * 60 + 30, 11 * 60),         # 10:30 to 11:00 -> (630, 660)
        (11 * 60 + 30, 12 * 60 + 30),    # 11:30 to 12:30 -> (690, 750)
        (13 * 60, 13 * 60 + 30),         # 13:00 to 13:30 -> (780, 810)
        (14 * 60 + 30, 15 * 60 + 30)     # 14:30 to 15:30 -> (870, 930) but we'll clip to our window end at 900.
        # The 16:00-16:30 meeting is outside our window.
    ]

    # Get free intervals for each participant within the scheduling window.
    lisa_free = get_free_intervals(lisa_busy, window_start, window_end)
    bobby_free = get_free_intervals(bobby_busy, window_start, window_end)
    randy_free = get_free_intervals(randy_busy, window_start, window_end)

    # Compute the common free intervals by intersecting them.
    common_free = intersect_intervals(lisa_free, bobby_free)
    common_free = intersect_intervals(common_free, randy_free)

    # Find a meeting slot of the required duration.
    slot = find_meeting_slot(common_free, meeting_duration)
    if slot:
        meeting_start, meeting_end = slot
        start_str = minutes_to_time(meeting_start)
        end_str = minutes_to_time(meeting_end)
        day = "Monday"
        # Output in the format HH:MM:HH:MM and the day of the week.
        print(f"{day} {start_str}:{end_str}")
    else:
        print("No available meeting slot found.")

if __name__ == "__main__":
    main()