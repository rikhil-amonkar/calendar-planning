def to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

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

def find_earliest_slot(merged_intervals):
    start_work = 540
    end_work = 1020

    if merged_intervals:
        first_start = merged_intervals[0][0]
        if first_start - start_work >= 60:
            return (start_work, start_work + 60)
    
    for i in range(len(merged_intervals) - 1):
        current_end = merged_intervals[i][1]
        next_start = merged_intervals[i+1][0]
        if next_start - current_end >= 60:
            return (current_end, current_end + 60)
    
    if merged_intervals:
        last_end = merged_intervals[-1][1]
        if end_work - last_end >= 60:
            return (last_end, last_end + 60)
    
    return None

brian = {
    'Monday': [
        (to_minutes('9:30'), to_minutes('10:00')),
        (to_minutes('12:30'), to_minutes('14:30')),
        (to_minutes('15:30'), to_minutes('16:00')),
    ],
    'Tuesday': [
        (to_minutes('9:00'), to_minutes('9:30')),
    ],
    'Wednesday': [
        (to_minutes('12:30'), to_minutes('14:00')),
        (to_minutes('16:30'), to_minutes('17:00')),
    ],
    'Thursday': [
        (to_minutes('11:00'), to_minutes('11:30')),
        (to_minutes('13:00'), to_minutes('13:30')),
        (to_minutes('16:30'), to_minutes('17:00')),
    ],
    'Friday': [
        (to_minutes('9:30'), to_minutes('10:00')),
        (to_minutes('10:30'), to_minutes('11:00')),
        (to_minutes('13:00'), to_minutes('13:30')),
        (to_minutes('15:00'), to_minutes('16:00')),
        (to_minutes('16:30'), to_minutes('17:00')),
    ],
}

julia = {
    'Monday': [
        (to_minutes('9:00'), to_minutes('10:00')),
        (to_minutes('11:00'), to_minutes('11:30')),
        (to_minutes('12:30'), to_minutes('13:00')),
        (to_minutes('15:30'), to_minutes('16:00')),
    ],
    'Tuesday': [
        (to_minutes('13:00'), to_minutes('14:00')),
        (to_minutes('16:00'), to_minutes('16:30')),
    ],
    'Wednesday': [
        (to_minutes('9:00'), to_minutes('11:30')),
        (to_minutes('12:00'), to_minutes('12:30')),
        (to_minutes('13:00'), to_minutes('17:00')),
    ],
    'Thursday': [
        (to_minutes('9:00'), to_minutes('10:30')),
        (to_minutes('11:00'), to_minutes('17:00')),
    ],
    'Friday': [
        (to_minutes('9:00'), to_minutes('10:00')),
        (to_minutes('10:30'), to_minutes('11:30')),
        (to_minutes('12:30'), to_minutes('14:00')),
        (to_minutes('14:30'), to_minutes('15:00')),
        (to_minutes('15:30'), to_minutes('16:00')),
    ],
}

days_order = ['Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Monday']

for day in days_order:
    brian_buses = brian.get(day, [])
    julia_buses = julia.get(day, [])
    all_buses = brian_buses + julia_buses
    merged = merge_intervals(all_buses)
    slot = find_earliest_slot(merged)
    if slot:
        start, end = slot
        start_str = to_time_str(start)
        end_str = to_time_str(end)
        print(f"{day} {start_str}:{end_str}")
        break