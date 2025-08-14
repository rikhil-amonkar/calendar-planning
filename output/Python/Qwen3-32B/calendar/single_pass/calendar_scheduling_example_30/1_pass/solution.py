def get_free_intervals(work_start, work_end, busy_intervals):
    busy_intervals.sort()
    free = []
    current = work_start
    for start, end in busy_intervals:
        if current < start:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(a, b):
    i = 0
    j = 0
    res = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            res.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return res

def main():
    work_start = 9 * 60
    work_end = 17 * 60

    # Busy intervals for each participant
    jeffrey_busy = [(570, 600), (630, 660)]
    virginia_busy = [(540, 570), (600, 630), (870, 900), (960, 990)]
    melissa_busy = [(540, 690), (720, 750), (780, 900), (960, 1020)]

    # Compute free intervals
    jeffrey_free = get_free_intervals(work_start, work_end, jeffrey_busy)
    virginia_free = get_free_intervals(work_start, work_end, virginia_busy)
    melissa_free = get_free_intervals(work_start, work_end, melissa_busy)

    # Find intersection of all three
    jv_intersect = intersect_intervals(jeffrey_free, virginia_free)
    all_free = intersect_intervals(jv_intersect, melissa_free)

    # Now find the earliest valid interval (>=30 min) that is before 14:00 if possible
    meeting_duration = 30  # minutes
    preferred_time = None
    for interval in all_free:
        start, end = interval
        duration = end - start
        if duration >= meeting_duration:
            meeting_end = start + meeting_duration
            if meeting_end <= 14 * 60:  # 14:00 is 840
                preferred_time = interval
                break  # earliest one first
    # If no preferred_time found, find the earliest one
    if preferred_time is None:
        for interval in all_free:
            start, end = interval
            duration = end - start
            if duration >= meeting_duration:
                preferred_time = interval
                break

    # Now, preferred_time is the interval to use
    start_time = preferred_time[0]
    end_time = start_time + meeting_duration

    # Convert to HH:MM format
    def to_time_str(m):
        h = m // 60
        mm = m % 60
        return f"{h:02d}:{mm:02d}"

    start_str = to_time_str(start_time)
    end_str = to_time_str(end_time)
    day = "Monday"
    print(f"{start_str}:{end_str} {day}")

if __name__ == "__main__":
    main()