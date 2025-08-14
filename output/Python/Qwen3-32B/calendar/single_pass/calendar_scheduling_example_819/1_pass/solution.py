work_start = 9 * 60  # 540 minutes (09:00)
work_end = 17 * 60   # 1020 minutes (17:00)

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def compute_available(busy_intervals, work_start, work_end):
    sorted_intervals = sorted(busy_intervals, key=lambda x: x[0])
    available = []
    prev_end = work_start
    for interval in sorted_intervals:
        current_start, current_end = interval
        if current_start > prev_end:
            available.append((prev_end, current_start))
        prev_end = max(prev_end, current_end)
    if prev_end < work_end:
        available.append((prev_end, work_end))
    return available

# Ruth's busy intervals per day (minutes since midnight)
ruth_schedule = {
    'Monday': [(540, 1020)],
    'Tuesday': [(540, 1020)],
    'Wednesday': [(540, 1020)],
    'Thursday': [(540, 660), (690, 870), (900, 1020)]
}

for day in ['Monday', 'Tuesday', 'Wednesday', 'Thursday']:
    busy_intervals = ruth_schedule[day]
    available_slots = compute_available(busy_intervals, work_start, work_end)
    for (start, end) in available_slots:
        duration = end - start
        if duration >= 30:
            if day == 'Thursday':
                # Julie avoids Thursday before 11:30 AM (690 minutes)
                if start >= 690:
                    start_time = minutes_to_time(start)
                    end_time = minutes_to_time(end)
                    print(f"{{{start_time}:{end_time}}} {day}")
                    exit()
            else:
                start_time = minutes_to_time(start)
                end_time = minutes_to_time(end)
                print(f"{{{start_time}:{end_time}}} {day}")
                exit()