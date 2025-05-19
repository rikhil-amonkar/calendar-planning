def time_to_min(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def min_to_time(minutes):
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

def find_slot():
    days_order = ['Monday', 'Tuesday', 'Wednesday']
    work_start = time_to_min('09:00')
    work_end = time_to_min('17:00')
    duration = 30

    schedules = {
        'Monday': {
            'Joshua': [(time_to_min('15:00'), time_to_min('15:30'))],
            'Joyce': [
                (time_to_min('09:00'), time_to_min('09:30')),
                (time_to_min('10:00'), time_to_min('11:00')),
                (time_to_min('11:30'), time_to_min('12:30')),
                (time_to_min('13:00'), time_to_min('15:00')),
                (time_to_min('15:30'), time_to_min('17:00'))
            ]
        },
        'Tuesday': {
            'Joshua': [
                (time_to_min('11:30'), time_to_min('12:00')),
                (time_to_min('13:00'), time_to_min('13:30')),
                (time_to_min('14:30'), time_to_min('15:00'))
            ],
            'Joyce': [(time_to_min('09:00'), time_to_min('17:00'))]
        },
        'Wednesday': {
            'Joshua': [],
            'Joyce': [
                (time_to_min('09:00'), time_to_min('09:30')),
                (time_to_min('10:00'), time_to_min('11:00')),
                (time_to_min('12:30'), time_to_min('15:30')),
                (time_to_min('16:00'), time_to_min('16:30'))
            ]
        }
    }

    for day in days_order:
        busy = []
        busy.extend(schedules[day]['Joshua'])
        busy.extend(schedules[day]['Joyce'])
        merged = merge_intervals(busy)
        free = []
        prev_end = work_start
        for start, end in merged:
            if start > prev_end:
                free.append((prev_end, start))
            prev_end = max(prev_end, end)
        if prev_end < work_end:
            free.append((prev_end, work_end))
        if day == 'Monday':
            free = [(s, e) for s, e in free if s >= time_to_min('12:00')]
        for start, end in free:
            if end - start >= duration:
                slot_start = start
                slot_end = slot_start + duration
                return (day, min_to_time(slot_start), min_to_time(slot_end))
    return None

result = find_slot()
if result:
    day, start, end = result
    print(f"{day} {start}-{end}")