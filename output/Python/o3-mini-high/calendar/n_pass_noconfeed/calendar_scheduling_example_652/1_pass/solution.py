def minutes_to_HHMM(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def merge_intervals(intervals):
    # Merge overlapping or contiguous intervals.
    intervals.sort(key=lambda x: x[0])
    merged = []
    for interval in intervals:
        if not merged:
            merged.append(interval)
        else:
            last = merged[-1]
            # if the current interval touches or overlaps the last, merge them
            if interval[0] <= last[1]:
                merged[-1] = (last[0], max(last[1], interval[1]))
            else:
                merged.append(interval)
    return merged

def get_free_intervals(work_start, work_end, busy_intervals):
    free = []
    current = work_start
    for (s, e) in busy_intervals:
        if s > current:
            free.append((current, s))
        current = max(current, e)
    if current < work_end:
        free.append((current, work_end))
    return free

def find_slot(free_intervals, meeting_duration):
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            return (start, start + meeting_duration)
    return None

def main():
    meeting_duration = 30  # meeting duration in minutes

    # Tuesday working hours: standard work is 9:00-17:00.
    # However, Lawrence cannot meet after 16:30 on Tuesday,
    # so the effective end of available time is 16:30.
    work_start = 9 * 60            # 9:00 AM -> 540 minutes
    work_end = 16 * 60 + 30        # 16:30 -> 990 minutes

    # Busy intervals for Tuesday (in minutes from 00:00)
    # Jesse's meetings on Tuesday:
    #   09:00-09:30 -> (540, 570)
    #   13:00-13:30 -> (780, 810)
    #   14:00-15:00 -> (840, 900)
    #
    # Lawrence's meetings on Tuesday:
    #   09:30-10:30 -> (570, 630)
    #   11:30-12:30 -> (690, 750)
    #   13:00-13:30 -> (780, 810)
    #   14:30-15:00 -> (870, 900)
    #   15:30-16:30 -> (930, 990)
    intervals = [
        (540, 570),  # Jesse 09:00-09:30
        (780, 810),  # Jesse 13:00-13:30
        (840, 900),  # Jesse 14:00-15:00
        (570, 630),  # Lawrence 09:30-10:30
        (690, 750),  # Lawrence 11:30-12:30
        (780, 810),  # Lawrence 13:00-13:30
        (870, 900),  # Lawrence 14:30-15:00
        (930, 990)   # Lawrence 15:30-16:30
    ]

    # Merge overlapping or contiguous busy intervals
    busy_intervals = merge_intervals(intervals)

    # Get the free intervals during Tuesday's available window
    free_intervals = get_free_intervals(work_start, work_end, busy_intervals)

    # Find the earliest free slot that can accommodate a 30-minute meeting
    slot = find_slot(free_intervals, meeting_duration)
    if slot is not None:
        start_str = minutes_to_HHMM(slot[0])
        end_str = minutes_to_HHMM(slot[1])
        # Output in the required format: Day HH:MM:HH:MM
        print(f"Tuesday {start_str}:{end_str}")
    else:
        print("No available meeting slot found on Tuesday.")

if __name__ == "__main__":
    main()