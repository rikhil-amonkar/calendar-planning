def get_available_intervals(work_start, work_end, busy_intervals):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    available = []
    prev_end = work_start
    for start, end in sorted_busy:
        if start > prev_end:
            available.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        available.append((prev_end, work_end))
    return available

def find_overlap(s_int, a_int, required_duration):
    s_start, s_end = s_int
    a_start, a_end = a_int
    overlap_start = max(s_start, a_start)
    overlap_end = min(s_end, a_end)
    if overlap_start < overlap_end:
        duration = overlap_end - overlap_start
        if duration >= required_duration:
            return (overlap_start, overlap_end)
    return None

WORK_START = 9 * 60
WORK_END = 17 * 60

shirley_busy = {
    'Monday': [
        (10*60 + 30, 11*60),
        (12*60, 12*60 + 30),
        (16*60, 16*60 + 30)
    ],
    'Tuesday': [
        (9*60 + 30, 10*60)
    ]
}

albert_busy = {
    'Monday': [
        (9*60, 17*60)
    ],
    'Tuesday': [
        (9*60 + 30, 11*60),
        (11*60 + 30, 12*60 + 30),
        (13*60, 16*60),
        (16*60 + 30, 17*60)
    ]
}

required_duration = 30  # minutes

days = ['Monday', 'Tuesday']

for day in days:
    shirley_b = shirley_busy.get(day, [])
    albert_b = albert_busy.get(day, [])
    
    shirley_available = get_available_intervals(WORK_START, WORK_END, shirley_b)
    albert_available = get_available_intervals(WORK_START, WORK_END, albert_b)
    
    if day == 'Tuesday':
        # Apply Shirley's preference: not after 10:30 (630 minutes)
        shirley_available_processed = []
        for interval in shirley_available:
            start, end = interval
            new_end = min(end, 630)
            if new_end > start:
                shirley_available_processed.append((start, new_end))
        shirley_available = shirley_available_processed
    
    # Check for overlaps
    for s_int in shirley_available:
        for a_int in albert_available:
            overlap = find_overlap(s_int, a_int, required_duration)
            if overlap:
                start_min, end_min = overlap
                def to_time(mins):
                    h = mins // 60
                    m = mins % 60
                    return f"{h:02d}:{m:02d}"
                start_time = to_time(start_min)
                end_time = to_time(end_min)
                print(f"{day} {start_time}:{end_time}")
                exit()