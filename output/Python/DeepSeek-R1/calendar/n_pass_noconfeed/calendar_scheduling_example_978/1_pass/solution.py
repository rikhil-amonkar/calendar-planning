def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy_intervals, day_start, day_end):
    if not busy_intervals:
        return [(day_start, day_end)]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current = day_start
    for s, e in sorted_busy:
        if current < s:
            free.append((current, s))
        current = max(current, e)
    if current < day_end:
        free.append((current, day_end))
    return free

def find_common_intervals(intervals1, intervals2):
    i, j = 0, 0
    common = []
    while i < len(intervals1) and j < len(intervals2):
        low = max(intervals1[i][0], intervals2[j][0])
        high = min(intervals1[i][1], intervals2[j][1])
        if low < high:
            common.append((low, high))
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return common

brian_busy = {
    'Monday': [
        (time_to_minutes('9:30'), time_to_minutes('10:00')),
        (time_to_minutes('12:30'), time_to_minutes('14:30')),
        (time_to_minutes('15:30'), time_to_minutes('16:00'))
    ],
    'Tuesday': [
        (time_to_minutes('9:00'), time_to_minutes('9:30'))
    ],
    'Wednesday': [
        (time_to_minutes('12:30'), time_to_minutes('14:00')),
        (time_to_minutes('16:30'), time_to_minutes('17:00'))
    ],
    'Thursday': [
        (time_to_minutes('11:00'), time_to_minutes('11:30')),
        (time_to_minutes('13:00'), time_to_minutes('13:30')),
        (time_to_minutes('16:30'), time_to_minutes('17:00'))
    ],
    'Friday': [
        (time_to_minutes('9:30'), time_to_minutes('10:00')),
        (time_to_minutes('10:30'), time_to_minutes('11:00')),
        (time_to_minutes('13:00'), time_to_minutes('13:30')),
        (time_to_minutes('15:00'), time_to_minutes('16:00')),
        (time_to_minutes('16:30'), time_to_minutes('17:00'))
    ]
}

julia_busy = {
    'Monday': [
        (time_to_minutes('9:00'), time_to_minutes('10:00')),
        (time_to_minutes('11:00'), time_to_minutes('11:30')),
        (time_to_minutes('12:30'), time_to_minutes('13:00')),
        (time_to_minutes('15:30'), time_to_minutes('16:00'))
    ],
    'Tuesday': [
        (time_to_minutes('13:00'), time_to_minutes('14:00')),
        (time_to_minutes('16:00'), time_to_minutes('16:30'))
    ],
    'Wednesday': [
        (time_to_minutes('9:00'), time_to_minutes('11:30')),
        (time_to_minutes('12:00'), time_to_minutes('12:30')),
        (time_to_minutes('13:00'), time_to_minutes('17:00'))
    ],
    'Thursday': [
        (time_to_minutes('9:00'), time_to_minutes('10:30')),
        (time_to_minutes('11:00'), time_to_minutes('17:00'))
    ],
    'Friday': [
        (time_to_minutes('9:00'), time_to_minutes('10:00')),
        (time_to_minutes('10:30'), time_to_minutes('11:30')),
        (time_to_minutes('12:30'), time_to_minutes('14:00')),
        (time_to_minutes('14:30'), time_to_minutes('15:00')),
        (time_to_minutes('15:30'), time_to_minutes('16:00'))
    ]
}

work_start = time_to_minutes('9:00')  # 540 minutes
work_end = time_to_minutes('17:00')    # 1020 minutes

days_order = ['Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Monday']

for day in days_order:
    brian_busy_today = brian_busy.get(day, [])
    julia_busy_today = julia_busy.get(day, [])
    
    brian_free = get_free_intervals(brian_busy_today, work_start, work_end)
    julia_free = get_free_intervals(julia_busy_today, work_start, work_end)
    
    common_free = find_common_intervals(brian_free, julia_free)
    
    for start, end in common_free:
        if end - start >= 60:
            meeting_start = start
            meeting_end = start + 60
            start_time_str = minutes_to_time(meeting_start)
            end_time_str = minutes_to_time(meeting_end)
            time_range_str = f"{start_time_str}:{end_time_str}"
            print(day)
            print(time_range_str)
            exit()

# If no solution is found (though the problem states there is one)
print("No suitable time found.")