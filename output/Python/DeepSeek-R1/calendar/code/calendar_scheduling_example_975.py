def parse_time(s):
    hours, minutes = map(int, s.split(':'))
    return hours * 60 + minutes

def to_time_str(minutes):
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

days_order = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']

nicole_busy = {
    'Tuesday': [(16*60, 16*60 + 30)],
    'Wednesday': [(15*60, 15*60 + 30)],
    'Friday': [
        (12*60, 12*60 + 30),
        (15*60 + 30, 16*60)
    ],
}

daniel_busy = {
    'Monday': [
        (9*60, 12*60 + 30),
        (13*60, 13*60 + 30),
        (14*60, 16*60 + 30)
    ],
    'Tuesday': [
        (9*60, 10*60 + 30),
        (11*60 + 30, 12*60 + 30),
        (13*60, 13*60 + 30),
        (15*60, 16*60),
        (16*60 + 30, 17*60)
    ],
    'Wednesday': [
        (9*60, 10*60),
        (11*60, 12*60 + 30),
        (13*60, 13*60 + 30),
        (14*60, 14*60 + 30),
        (16*60 + 30, 17*60)
    ],
    'Thursday': [
        (11*60, 12*60),
        (13*60, 14*60),
        (15*60, 15*60 + 30)
    ],
    'Friday': [
        (10*60, 11*60),
        (11*60 + 30, 12*60),
        (12*60 + 30, 14*60 + 30),
        (15*60, 15*60 + 30),
        (16*60, 16*60 + 30)
    ]
}

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals)
    merged = [sorted_intervals[0]]
    for current in sorted_intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def get_free_intervals(busy_intervals, day):
    day_start = 9 * 60
    day_end = 17 * 60
    intervals = busy_intervals.get(day, [])
    merged = merge_intervals(intervals)
    free = []
    prev_end = day_start
    for start, end in merged:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = end
    if prev_end < day_end:
        free.append((prev_end, day_end))
    return free

def find_meeting_slot():
    for day in days_order:
        nicole_free = get_free_intervals(nicole_busy, day)
        daniel_free = get_free_intervals(daniel_busy, day)
        for n_start, n_end in nicole_free:
            for d_start, d_end in daniel_free:
                overlap_start = max(n_start, d_start)
                overlap_end = min(n_end, d_end)
                if overlap_end - overlap_start >= 60:
                    return (
                        day,
                        (overlap_start, overlap_start + 60)
                    )
    return None

result = find_meeting_slot()
if result:
    day, (start, end) = result
    print(f"{day}:{to_time_str(start)}:{to_time_str(end)}")
else:
    print("No slot found")