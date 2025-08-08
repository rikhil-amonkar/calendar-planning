def free_intervals(busy, work_start, work_end):
    """Given sorted busy intervals, return the free intervals within work_start and work_end."""
    free = []
    last = work_start
    for start, end in busy:
        if start > last:
            free.append((last, start))
        last = max(last, end)
    if last < work_end:
        free.append((last, work_end))
    return free

def intersect_intervals(list1, list2):
    """Return the intersection of two lists of intervals."""
    result = []
    i, j = 0, 0
    while i < len(list1) and j < len(list2):
        a, b = list1[i]
        c, d = list2[j]
        start = max(a, c)
        end = min(b, d)
        if start < end:
            result.append((start, end))
        if b < d:
            i += 1
        else:
            j += 1
    return result

def minutes_to_str(minutes):
    """Convert minutes since midnight to HH:MM string format."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    # Define working hours (in minutes past midnight)
    work_start = 9 * 60    # 9:00 -> 540 minutes
    work_end = 17 * 60     # 17:00 -> 1020 minutes
    meeting_duration = 30  # in minutes

    # Busy intervals for each participant (in minutes past midnight)
    # Cynthia: busy from 9:30-10:30, 11:30-12:00, 13:00-13:30, 15:00-16:00.
    cynthia_busy = [(9*60+30, 10*60+30), (11*60+30, 12*60), (13*60, 13*60+30), (15*60, 16*60)]
    # Lauren: busy from 9:00-9:30, 10:30-11:00, 11:30-12:00, 13:00-13:30,
    # 14:00-14:30, 15:00-15:30, and 16:00-17:00.
    lauren_busy = [(9*60, 9*60+30), (10*60+30, 11*60), (11*60+30, 12*60),
                   (13*60, 13*60+30), (14*60, 14*60+30), (15*60, 15*60+30), (16*60, 17*60)]
    # Robert: busy from 10:30-11:00, 11:30-12:00, 12:30-13:30, and 14:00-16:00.
    robert_busy = [(10*60+30, 11*60), (11*60+30, 12*60), (12*60+30, 13*60+30), (14*60, 16*60)]
    # Steven and Roy are free all day.
    steven_busy = []
    roy_busy = []

    # Calculate free intervals for each participant
    steven_free = free_intervals(steven_busy, work_start, work_end)
    roy_free = free_intervals(roy_busy, work_start, work_end)
    cynthia_free = free_intervals(cynthia_busy, work_start, work_end)
    lauren_free = free_intervals(lauren_busy, work_start, work_end)
    robert_free = free_intervals(robert_busy, work_start, work_end)

    # Start with the full working hours as the initial common free slot.
    common_free = [(work_start, work_end)]
    # Intersect with each participant's free intervals.
    for free in [steven_free, roy_free, cynthia_free, lauren_free, robert_free]:
        common_free = intersect_intervals(common_free, free)

    # Find the earliest common free interval that can accommodate the meeting duration.
    meeting_start = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_start = start
            break

    if meeting_start is None:
        print("No common time slot available")
        return

    meeting_end = meeting_start + meeting_duration
    day_of_week = "Monday"
    # Format the meeting time as HH:MM:HH:MM.
    meeting_time_str = f"{minutes_to_str(meeting_start)}:{minutes_to_str(meeting_end)}"
    print(f"{day_of_week} {meeting_time_str}")

if __name__ == "__main__":
    main()