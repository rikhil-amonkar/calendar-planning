def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = []
    start, end = sorted_intervals[0]
    for i in range(1, len(sorted_intervals)):
        s, e = sorted_intervals[i]
        if s <= end:
            if e > end:
                end = e
        else:
            merged.append((start, end))
            start, end = s, e
    merged.append((start, end))
    return merged

bobby_busy = {
    'Monday': [('14:30', '15:00')],
    'Tuesday': [('9:00', '11:30'), ('12:00', '12:30'), ('13:00', '15:00'), ('15:30', '17:00')]
}

michael_busy = {
    'Monday': [('9:00', '10:00'), ('10:30', '13:30'), ('14:00', '15:00'), ('15:30', '17:00')],
    'Tuesday': [('9:00', '10:30'), ('11:00', '11:30'), ('12:00', '14:00'), ('15:00', '16:00'), ('16:30', '17:00')]
}

work_start_min = 540  # 9:00
work_end_min = 1020   # 17:00

days = ['Monday', 'Tuesday']

for day in days:
    b_intervals = bobby_busy[day]
    m_intervals = michael_busy[day]
    all_busy = []
    for interval in b_intervals:
        s, e = interval
        s_min = time_to_minutes(s)
        e_min = time_to_minutes(e)
        all_busy.append((s_min, e_min))
    for interval in m_intervals:
        s, e = interval
        s_min = time_to_minutes(s)
        e_min = time_to_minutes(e)
        all_busy.append((s_min, e_min))
    
    merged_busy = merge_intervals(all_busy)
    
    free_intervals = []
    current = work_start_min
    for start, end in merged_busy:
        if current < start:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end_min:
        free_intervals.append((current, work_end_min))
    
    for start_free, end_free in free_intervals:
        duration = end_free - start_free
        if duration >= 30:
            meeting_start = start_free
            meeting_end = start_free + 30
            start_str = minutes_to_time(meeting_start)
            end_str = minutes_to_time(meeting_end)
            print(f"{start_str}:{end_str}")
            print(day)
            exit(0)

print("No meeting time found")
exit(1)