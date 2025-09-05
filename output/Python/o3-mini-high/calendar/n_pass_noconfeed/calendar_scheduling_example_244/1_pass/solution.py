def minutes_to_time(minutes):
    """Convert minutes since midnight into a string in HH:MM format."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    """
    Given a sorted list of busy intervals (start, end) and a work window,
    returns a list of free intervals within the work window.
    """
    free = []
    current = work_start
    for b, e in sorted(busy_intervals, key=lambda x: x[0]):
        if current < b:
            free.append((current, b))
        if e > current:
            current = e
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_two(intervals1, intervals2):
    """
    Given two lists of intervals, return their intersection.
    Assumes each list is sorted by interval start.
    """
    result = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        a_start, a_end = intervals1[i]
        b_start, b_end = intervals2[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            result.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return result

def intersect_all(lists_of_intervals):
    """
    Intersect a list of interval lists.
    """
    if not lists_of_intervals:
        return []
    common = lists_of_intervals[0]
    for intervals in lists_of_intervals[1:]:
        common = intersect_two(common, intervals)
    return common

def main():
    # Define work day start and end in minutes (9:00 to 17:00)
    work_start = 9 * 60   # 9:00 is 540 minutes
    work_end = 17 * 60    # 17:00 is 1020 minutes
    meeting_duration = 30  # duration is 30 minutes

    # Define busy schedules (in minutes since midnight) for each participant on Monday.
    # Walter is free all day.
    walter_busy = []

    # Cynthia's meetings: 9:00-9:30, 10:00-10:30, 13:30-14:30, 15:00-16:00
    cynthia_busy = [
        (9 * 60, 9 * 60 + 30),
        (10 * 60, 10 * 60 + 30),
        (13 * 60 + 30, 14 * 60 + 30),
        (15 * 60, 16 * 60)
    ]

    # Ann's meetings: 10:00-11:00, 13:00-13:30, 14:00-15:00, 16:00-16:30
    ann_busy = [
        (10 * 60, 11 * 60),
        (13 * 60, 13 * 60 + 30),
        (14 * 60, 15 * 60),
        (16 * 60, 16 * 60 + 30)
    ]

    # Catherine's meetings: 9:00-11:30, 12:30-13:30, 14:30-17:00
    catherine_busy = [
        (9 * 60, 11 * 60 + 30),
        (12 * 60 + 30, 13 * 60 + 30),
        (14 * 60 + 30, 17 * 60)
    ]

    # Kyle's meetings: 9:00-9:30, 10:00-11:30, 12:00-12:30, 13:00-14:30, 15:00-16:00
    kyle_busy = [
        (9 * 60, 9 * 60 + 30),
        (10 * 60, 11 * 60 + 30),
        (12 * 60, 12 * 60 + 30),
        (13 * 60, 14 * 60 + 30),
        (15 * 60, 16 * 60)
    ]

    # Calculate free intervals for each participant.
    walter_free = get_free_intervals(walter_busy, work_start, work_end)
    cynthia_free = get_free_intervals(cynthia_busy, work_start, work_end)
    ann_free = get_free_intervals(ann_busy, work_start, work_end)
    catherine_free = get_free_intervals(catherine_busy, work_start, work_end)
    kyle_free = get_free_intervals(kyle_busy, work_start, work_end)

    # Compute the common free intervals for all participants.
    all_free = [walter_free, cynthia_free, ann_free, catherine_free, kyle_free]
    common_free = intersect_all(all_free)

    # Find an available time slot that fits the meeting duration.
    meeting_start = None
    for interval in common_free:
        start, end = interval
        if end - start >= meeting_duration:
            meeting_start = start
            break

    if meeting_start is not None:
        meeting_end = meeting_start + meeting_duration
        start_str = minutes_to_time(meeting_start)
        end_str = minutes_to_time(meeting_end)
        # Output the scheduled meeting time in HH:MM:HH:MM format with the day of the week.
        print("Monday", f"{start_str}:{end_str}")
    else:
        print("No common time slot available.")

if __name__ == "__main__":
    main()