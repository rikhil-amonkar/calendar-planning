def time_to_minutes(t):
    """Converts a time string "HH:MM" to minutes since midnight."""
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Converts minutes since midnight to a time string "HH:MM"."""
    return f"{m // 60:02d}:{m % 60:02d}"

def compute_free_intervals(busy_intervals, work_start, work_end):
    """
    Given a sorted list of busy intervals (tuples of start,end in minutes),
    computes the free intervals within the work window [work_start, work_end].
    Busy intervals that fall partially outside are clipped to the work window.
    """
    free = []
    current = work_start
    for interval in busy_intervals:
        # Clip busy interval to work window
        busy_start = max(interval[0], work_start)
        busy_end = min(interval[1], work_end)
        if busy_start > current:
            free.append((current, busy_start))
        # Move current pointer forward if busy overlaps
        if busy_end > current:
            current = busy_end
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(list1, list2):
    """
    Intersect two lists of intervals.
    Each interval is a tuple (start, end) in minutes.
    Returns a new list of intervals that are common to both lists.
    """
    result = []
    i, j = 0, 0
    while i < len(list1) and j < len(list2):
        start1, end1 = list1[i]
        start2, end2 = list2[j]
        # Find the overlap between intervals
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            result.append((start_overlap, end_overlap))
        # Move forward in the list of the interval that ends first
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

def main():
    # Meeting parameters
    meeting_duration = 30  # minutes
    day_of_week = "Monday"
    # Working hours originally 9:00 to 17:00, but Jose prefers not after 15:30.
    # Therefore, restrict meeting so that it ends by 15:30.
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("15:30")  # meeting must finish by 15:30

    # Define busy intervals for each participant as (start_minute, end_minute)
    # Times are given in "HH:MM" format and then converted to minutes.
    participants_busy = {
        "Jose": [
            (time_to_minutes("11:00"), time_to_minutes("11:30")),
            (time_to_minutes("12:30"), time_to_minutes("13:00"))
        ],
        "Keith": [
            (time_to_minutes("14:00"), time_to_minutes("14:30")),
            (time_to_minutes("15:00"), time_to_minutes("15:30"))
        ],
        "Logan": [
            (time_to_minutes("09:00"), time_to_minutes("10:00")),
            (time_to_minutes("12:00"), time_to_minutes("12:30")),
            (time_to_minutes("15:00"), time_to_minutes("15:30"))
        ],
        "Megan": [
            (time_to_minutes("09:00"), time_to_minutes("10:30")),
            (time_to_minutes("11:00"), time_to_minutes("12:00")),
            (time_to_minutes("13:00"), time_to_minutes("13:30")),
            (time_to_minutes("14:30"), time_to_minutes("16:30"))
        ],
        "Gary": [
            (time_to_minutes("09:00"), time_to_minutes("09:30")),
            (time_to_minutes("10:00"), time_to_minutes("10:30")),
            (time_to_minutes("11:30"), time_to_minutes("13:00")),
            (time_to_minutes("13:30"), time_to_minutes("14:00")),
            (time_to_minutes("14:30"), time_to_minutes("16:30"))
        ],
        "Bobby": [
            (time_to_minutes("11:00"), time_to_minutes("11:30")),
            (time_to_minutes("12:00"), time_to_minutes("12:30")),
            (time_to_minutes("13:00"), time_to_minutes("16:00"))
        ]
    }

    # Compute free intervals for each participant by subtracting busy intervals from the working window.
    free_intervals_by_person = {}
    for person, busy in participants_busy.items():
        # Sort busy intervals in case they are not in order.
        busy_sorted = sorted(busy, key=lambda x: x[0])
        free_intervals_by_person[person] = compute_free_intervals(busy_sorted, work_start, work_end)
    
    # Compute the common free intervals across all participants.
    common_free = None
    for person, free_list in free_intervals_by_person.items():
        if common_free is None:
            common_free = free_list
        else:
            common_free = intersect_intervals(common_free, free_list)

    # Find the earliest interval that can accommodate the meeting duration.
    meeting_time = None
    for interval in common_free:
        start, end = interval
        if end - start >= meeting_duration:
            meeting_time = (start, start + meeting_duration)
            break

    if meeting_time:
        start_str = minutes_to_time(meeting_time[0])
        end_str = minutes_to_time(meeting_time[1])
        # Output in the required format: "HH:MM:HH:MM" along with the day of the week.
        print(f"{day_of_week} {start_str}:{end_str}")
    else:
        print("No available meeting time found.")

if __name__ == "__main__":
    main()