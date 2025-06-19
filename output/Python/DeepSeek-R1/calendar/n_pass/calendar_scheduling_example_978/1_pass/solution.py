def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_list, work_start, work_end):
    intervals = []
    for s, e in busy_list:
        s_min = time_str_to_minutes(s)
        e_min = time_str_to_minutes(e)
        intervals.append((s_min, e_min))
    
    if not intervals:
        return [[work_start, work_end]]
    
    intervals.sort(key=lambda x: x[0])
    merged = []
    current_start, current_end = intervals[0]
    for i in range(1, len(intervals)):
        s, e = intervals[i]
        if s <= current_end:
            current_end = max(current_end, e)
        else:
            merged.append([current_start, current_end])
            current_start, current_end = s, e
    merged.append([current_start, current_end])
    
    free = []
    start = work_start
    for interval in merged:
        if start < interval[0]:
            free.append([start, interval[0]])
        start = interval[1]
    if start < work_end:
        free.append([start, work_end])
    
    return free

def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    common = []
    while i < len(intervals1) and j < len(intervals2):
        low = max(intervals1[i][0], intervals2[j][0])
        high = min(intervals1[i][1], intervals2[j][1])
        if low < high:
            common.append([low, high])
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return common

def main():
    work_start = 540  # 9:00
    work_end = 1020    # 17:00
    duration = 60

    brian_busy = {
        'Monday': [('9:30', '10:00'), ('12:30', '14:30'), ('15:30', '16:00')],
        'Tuesday': [('9:00', '9:30')],
        'Wednesday': [('12:30', '14:00'), ('16:30', '17:00')],
        'Thursday': [('11:00', '11:30'), ('13:00', '13:30'), ('16:30', '17:00')],
        'Friday': [('9:30', '10:00'), ('10:30', '11:00'), ('13:00', '13:30'), ('15:00', '16:00'), ('16:30', '17:00')]
    }
    
    julia_busy = {
        'Monday': [('9:00', '10:00'), ('11:00', '11:30'), ('12:30', '13:00'), ('15:30', '16:00')],
        'Tuesday': [('13:00', '14:00'), ('16:00', '16:30')],
        'Wednesday': [('9:00', '11:30'), ('12:00', '12:30'), ('13:00', '17:00')],
        'Thursday': [('9:00', '10:30'), ('11:00', '17:00')],
        'Friday': [('9:00', '10:00'), ('10:30', '11:30'), ('12:30', '14:00'), ('14:30', '15:00'), ('15:30', '16:00')]
    }
    
    day_order = ['Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Monday']
    
    for day in day_order:
        brian_list = brian_busy.get(day, [])
        julia_list = julia_busy.get(day, [])
        
        free_brian = get_free_intervals(brian_list, work_start, work_end)
        free_julia = get_free_intervals(julia_list, work_start, work_end)
        
        common_free = intersect_intervals(free_brian, free_julia)
        
        for interval in common_free:
            start, end = interval
            if end - start >= duration:
                start_time_str = minutes_to_time_str(start)
                end_time_str = minutes_to_time_str(start + duration)
                print(f"{start_time_str}:{end_time_str}")
                print(day)
                return

if __name__ == "__main__":
    main()