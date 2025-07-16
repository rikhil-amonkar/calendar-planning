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
    for interval in sorted_intervals[1:]:
        if interval[0] <= end:
            if interval[1] > end:
                end = interval[1]
        else:
            merged.append((start, end))
            start, end = interval
    merged.append((start, end))
    return merged

days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']

busy_times = {
    'Nicole': {
        'Tuesday': [('16:00', '16:30')],
        'Wednesday': [('15:00', '15:30')],
        'Friday': [('12:00', '12:30'), ('15:30', '16:00')]
    },
    'Daniel': {
        'Monday': [('09:00', '12:30'), ('13:00', '13:30'), ('14:00', '16:30')],
        'Tuesday': [('09:00', '10:30'), ('11:30', '12:30'), ('13:00', '13:30'), ('15:00', '16:00'), ('16:30', '17:00')],
        'Wednesday': [('09:00', '10:00'), ('11:00', '12:30'), ('13:00', '13:30'), ('14:00', '14:30'), ('16:30', '17:00')],
        'Thursday': [('11:00', '12:00'), ('13:00', '14:00'), ('15:00', '15:30')],
        'Friday': [('10:00', '11:00'), ('11:30', '12:00'), ('12:30', '14:30'), ('15:00', '15:30'), ('16:00', '16:30')]
    }
}

work_start = time_to_minutes('09:00')
work_end = time_to_minutes('17:00')
meeting_duration = 60

found = False
result_day = None
result_start = None

for day in days:
    all_busy_intervals = []
    
    for person in ['Nicole', 'Daniel']:
        if day in busy_times[person]:
            for interval in busy_times[person][day]:
                start_min = time_to_minutes(interval[0])
                end_min = time_to_minutes(interval[1])
                all_busy_intervals.append((start_min, end_min))
    
    if not all_busy_intervals:
        slot_start = work_start
        slot_end = work_start + meeting_duration
        if slot_end <= work_end:
            result_day = day
            result_start = slot_start
            found = True
            break
    else:
        merged_busy = merge_intervals(all_busy_intervals)
        current_time = work_start
        for busy_start, busy_end in merged_busy:
            if current_time + meeting_duration <= busy_start:
                slot_start = current_time
                slot_end = current_time + meeting_duration
                if slot_end <= work_end:
                    result_day = day
                    result_start = slot_start
                    found = True
                    break
            current_time = max(current_time, busy_end)
        if found:
            break
        if current_time + meeting_duration <= work_end:
            slot_start = current_time
            slot_end = current_time + meeting_duration
            result_day = day
            result_start = slot_start
            found = True
            break
    if found:
        break

if found:
    start_time_str = minutes_to_time(result_start)
    end_time_str = minutes_to_time(result_start + meeting_duration)
    print(f"{result_day}:{start_time_str}:{end_time_str}")
else:
    print("No suitable time slot found.")