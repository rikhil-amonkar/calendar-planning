def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def compute_free_intervals(busy_intervals, work_start, work_end):
    if not busy_intervals:
        return [(work_start, work_end)]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current = work_start
    for s, e in sorted_busy:
        if current < s:
            free.append((current, s))
        current = max(current, e)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals_a, intervals_b):
    i = j = 0
    result = []
    while i < len(intervals_a) and j < len(intervals_b):
        low = max(intervals_a[i][0], intervals_b[j][0])
        high = min(intervals_a[i][1], intervals_b[j][1])
        if low < high:
            result.append((low, high))
        if intervals_a[i][1] < intervals_b[j][1]:
            i += 1
        else:
            j += 1
    return result

def main():
    work_start_min = time_str_to_minutes("9:00")
    work_end_min = time_str_to_minutes("12:30")  # meeting must end by 12:30
    duration_min = 60

    ryan_busy_str = [("9:00", "9:30"), ("12:30", "13:00")]
    ruth_busy_str = []
    denise_busy_str = [("9:30", "10:30"), ("12:00", "13:00"), ("14:30", "16:30")]

    ryan_busy_min = []
    for s, e in ryan_busy_str:
        s_min = time_str_to_minutes(s)
        e_min = time_str_to_minutes(e)
        s_min = max(s_min, work_start_min)
        e_min = min(e_min, work_end_min)
        if s_min < e_min:
            ryan_busy_min.append((s_min, e_min))

    ruth_busy_min = []
    for s, e in ruth_busy_str:
        s_min = time_str_to_minutes(s)
        e_min = time_str_to_minutes(e)
        s_min = max(s_min, work_start_min)
        e_min = min(e_min, work_end_min)
        if s_min < e_min:
            ruth_busy_min.append((s_min, e_min))

    denise_busy_min = []
    for s, e in denise_busy_str:
        s_min = time_str_to_minutes(s)
        e_min = time_str_to_minutes(e)
        s_min = max(s_min, work_start_min)
        e_min = min(e_min, work_end_min)
        if s_min < e_min:
            denise_busy_min.append((s_min, e_min))

    free_ryan = compute_free_intervals(ryan_busy_min, work_start_min, work_end_min)
    free_ruth = compute_free_intervals(ruth_busy_min, work_start_min, work_end_min)
    free_denise = compute_free_intervals(denise_busy_min, work_start_min, work_end_min)

    common = intersect_intervals(free_ryan, free_ruth)
    common = intersect_intervals(common, free_denise)

    meeting_start = None
    for s, e in common:
        if e - s >= duration_min:
            meeting_start = s
            break

    if meeting_start is None:
        print("No solution found")
        return

    meeting_end = meeting_start + duration_min
    start_str = minutes_to_time_str(meeting_start)
    end_str = minutes_to_time_str(meeting_end)
    time_range_str = start_str + ':' + end_str

    print("Monday")
    print(time_range_str)

if __name__ == "__main__":
    main()