def to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = [sorted_intervals[0]]
    for current in sorted_intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def get_free_intervals(merged_busy, work_start, work_end):
    free = []
    prev_end = work_start
    for interval in merged_busy:
        start, end = interval
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def main():
    busy_intervals = []
    # Judy
    busy_intervals.extend([(780, 810), (960, 990)])
    # Olivia
    busy_intervals.extend([(600, 630), (720, 780), (840, 870)])
    # Jacqueline
    busy_intervals.extend([(600, 630), (900, 930)])
    # Laura
    busy_intervals.extend([(540, 600), (630, 720), (780, 810), (870, 900), (930, 1020)])
    # Tyler
    busy_intervals.extend([(540, 600), (660, 690), (750, 780), (840, 870), (930, 1020)])
    # Lisa
    busy_intervals.extend([(570, 630), (660, 690), (720, 750), (780, 810), (840, 870), (960, 1020)])
    
    merged_busy = merge_intervals(busy_intervals)
    work_start = 540  # 9:00
    work_end = 1020   # 17:00
    
    free_intervals = get_free_intervals(merged_busy, work_start, work_end)
    
    for s, e in free_intervals:
        if e - s >= 30:
            meeting_start = s
            meeting_end = s + 30
            start_time = to_time(meeting_start)
            end_time = to_time(meeting_end)
            day = "Monday"
            print(f"{{{start_time}:{end_time}}} {day}")
            return

if __name__ == "__main__":
    main()