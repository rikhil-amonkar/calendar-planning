def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def compute_free_intervals(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free_intervals = []
    current = work_start
    for s, e in sorted_busy:
        if current < s:
            free_intervals.append((current, s))
        current = e
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

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
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 60
    
    # Julie's busy intervals
    julie_busy = [
        ("9:00", "9:30"),
        ("11:00", "11:30"),
        ("12:00", "12:30"),
        ("13:30", "14:00"),
        ("16:00", "17:00")
    ]
    julie_busy_minutes = [(time_to_minutes(s), time_to_minutes(e)) for s, e in julie_busy]
    free_julie = compute_free_intervals(julie_busy_minutes, work_start, work_end)
    
    # Sean's busy intervals
    sean_busy = [
        ("9:00", "9:30"),
        ("13:00", "13:30"),
        ("15:00", "15:30"),
        ("16:00", "16:30")
    ]
    sean_busy_minutes = [(time_to_minutes(s), time_to_minutes(e)) for s, e in sean_busy]
    free_sean = compute_free_intervals(sean_busy_minutes, work_start, work_end)
    
    # Lori's busy intervals
    lori_busy = [
        ("10:00", "10:30"),
        ("11:00", "13:00"),
        ("15:30", "17:00")
    ]
    lori_busy_minutes = [(time_to_minutes(s), time_to_minutes(e)) for s, e in lori_busy]
    free_lori = compute_free_intervals(lori_busy_minutes, work_start, work_end)
    
    common_free = intersect_intervals(free_julie, free_sean)
    common_free = intersect_intervals(common_free, free_lori)
    
    meeting_start = None
    meeting_end = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            break
    
    if meeting_start is None:
        print("No suitable time found")
    else:
        start_str = minutes_to_time(meeting_start)
        end_str = minutes_to_time(meeting_end)
        print("Monday")
        print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()