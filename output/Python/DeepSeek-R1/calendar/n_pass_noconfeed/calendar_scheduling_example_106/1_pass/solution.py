def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return (hour - 9) * 60 + minute

def minutes_to_time(minutes):
    total_minutes = 9 * 60 + minutes
    hour = total_minutes // 60
    minute = total_minutes % 60
    return hour, minute

def compute_free_intervals(busy_intervals, work_start, work_end):
    if not busy_intervals:
        return [(work_start, work_end)]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    merged = []
    start_curr, end_curr = sorted_busy[0]
    for i in range(1, len(sorted_busy)):
        s, e = sorted_busy[i]
        if s <= end_curr:
            if e > end_curr:
                end_curr = e
        else:
            merged.append((start_curr, end_curr))
            start_curr, end_curr = s, e
    merged.append((start_curr, end_curr))
    free = []
    current = work_start
    for interval in merged:
        s, e = interval
        if current < s:
            free.append((current, s))
        current = e
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    i = j = 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        low = max(intervals1[i][0], intervals2[j][0])
        high = min(intervals1[i][1], intervals2[j][1])
        if low < high:
            result.append((low, high))
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return result

def main():
    work_start = 0
    work_end = 480
    olivia_busy = [
        (time_to_minutes("12:30"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    anna_busy = []
    virginia_busy = [
        (time_to_minutes("9:00"), time_to_minutes("10:00")),
        (time_to_minutes("11:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    paul_busy = [
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("13:00"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    persons_busy = [olivia_busy, anna_busy, virginia_busy, paul_busy]
    persons_free = []
    for busy in persons_busy:
        free_intervals = compute_free_intervals(busy, work_start, work_end)
        persons_free.append(free_intervals)
    common = persons_free[0]
    for i in range(1, len(persons_free)):
        common = intersect_intervals(common, persons_free[i])
    meeting_start = None
    for interval in common:
        start, end = interval
        if end - start >= 60:
            meeting_start = start
            break
    if meeting_start is None:
        return
    start_hour, start_minute = minutes_to_time(meeting_start)
    end_hour, end_minute = minutes_to_time(meeting_start + 60)
    print("Monday")
    print(f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")

if __name__ == "__main__":
    main()