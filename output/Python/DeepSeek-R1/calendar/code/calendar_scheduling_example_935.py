def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
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

def find_slot(terry, frances):
    days_order = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    
    for day in days_order:
        terry_busy = terry.get(day, [])
        frances_busy = frances.get(day, [])
        all_busy = terry_busy + frances_busy
        intervals = []
        for start, end in all_busy:
            intervals.append((start, end))
        merged = merge_intervals(intervals)
        free = []
        prev_end = work_start
        for start, end in merged:
            if start > prev_end:
                free.append((prev_end, start))
            prev_end = max(prev_end, end)
        if prev_end < work_end:
            free.append((prev_end, work_end))
        for start, end in free:
            if end - start >= 30:
                return (day, start, start + 30)
    return None

terry_schedule = {
    "Monday": [
        ("10:30", "11:00"),
        ("12:30", "14:00"),
        ("15:00", "17:00")
    ],
    "Tuesday": [
        ("9:30", "10:00"),
        ("10:30", "11:00"),
        ("14:00", "14:30"),
        ("16:00", "16:30")
    ],
    "Wednesday": [
        ("9:30", "10:30"),
        ("11:00", "12:00"),
        ("13:00", "13:30"),
        ("15:00", "16:00"),
        ("16:30", "17:00")
    ],
    "Thursday": [
        ("9:30", "10:00"),
        ("12:00", "12:30"),
        ("13:00", "14:30"),
        ("16:00", "16:30")
    ],
    "Friday": [
        ("9:00", "11:30"),
        ("12:00", "12:30"),
        ("13:30", "16:00"),
        ("16:30", "17:00")
    ]
}

frances_schedule = {
    "Monday": [
        ("9:30", "11:00"),
        ("11:30", "13:00"),
        ("14:00", "14:30"),
        ("15:00", "16:00")
    ],
    "Tuesday": [
        ("9:00", "9:30"),
        ("10:00", "10:30"),
        ("11:00", "12:00"),
        ("13:00", "14:30"),
        ("15:30", "16:30")
    ],
    "Wednesday": [
        ("9:30", "10:00"),
        ("10:30", "11:00"),
        ("11:30", "16:00"),
        ("16:30", "17:00")
    ],
    "Thursday": [
        ("11:00", "12:30"),
        ("14:30", "17:00")
    ],
    "Friday": [
        ("9:30", "10:30"),
        ("11:00", "12:30"),
        ("13:00", "16:00"),
        ("16:30", "17:00")
    ]
}

terry = {day: [(time_to_minutes(s), time_to_minutes(e)) for s, e in intervals] for day, intervals in terry_schedule.items()}
frances = {day: [(time_to_minutes(s), time_to_minutes(e)) for s, e in intervals] for day, intervals in frances_schedule.items()}

result = find_slot(terry, frances)
if result:
    day, start, end = result
    print(f"{day} {minutes_to_time(start)}:{minutes_to_time(end)}")
else:
    print("No slot found")