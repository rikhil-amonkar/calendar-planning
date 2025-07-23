def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time_str(minutes):
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
            end = max(end, e)
        else:
            merged.append((start, end))
            start, end = s, e
    merged.append((start, end))
    return merged

def subtract_busy(work_start, work_end, busy_intervals):
    if not busy_intervals:
        return [(work_start, work_end)]
    merged_busy = merge_intervals(busy_intervals)
    free = []
    current = work_start
    for interval in merged_busy:
        if current < interval[0]:
            free.append((current, interval[0]))
        current = max(current, interval[1])
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_two_intervals(intervals1, intervals2):
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
    work_start = time_str_to_minutes("9:00")
    work_end = time_str_to_minutes("17:00")
    meeting_duration = 30
    
    busy_times = {
        'Patrick': [('9:00', '9:30'), ('10:00','10:30'), ('13:30','14:00'), ('16:00','16:30')],
        'Kayla': [('12:30','13:30'), ('15:00','15:30'), ('16:00','16:30')],
        'Carl': [('10:30','11:00'), ('12:00','12:30'), ('13:00','13:30'), ('14:30','17:00')],
        'Christian': [('9:00','12:30'), ('13:00','14:00'), ('14:30','17:00')]
    }
    
    # Convert busy times to minutes
    busy_minutes = {}
    for person, intervals in busy_times.items():
        busy_minutes[person] = []
        for start, end in intervals:
            busy_minutes[person].append((time_str_to_minutes(start), time_str_to_minutes(end)))
    
    # Calculate free intervals for each person
    free_intervals = {}
    for person in busy_minutes:
        free_intervals[person] = subtract_busy(work_start, work_end, busy_minutes[person])
    
    # Find common free intervals
    common_free = free_intervals['Patrick']
    for person in ['Kayla', 'Carl', 'Christian']:
        common_free = intersect_two_intervals(common_free, free_intervals[person])
    
    # Find the first slot of at least meeting_duration
    meeting_start = None
    meeting_end = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            break
    
    # Convert to time strings
    start_str = minutes_to_time_str(meeting_start)
    end_str = minutes_to_time_str(meeting_end)
    
    print("Monday")
    print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()