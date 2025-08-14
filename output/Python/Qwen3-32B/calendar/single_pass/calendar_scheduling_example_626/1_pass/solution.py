def get_free_intervals(busy_intervals, start_work, end_work):
    free_intervals = []
    current_start = start_work
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    for start, end in sorted_busy:
        if current_start < start:
            free_intervals.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < end_work:
        free_intervals.append((current_start, end_work))
    return free_intervals

def interval_intersection(int1, int2):
    start = max(int1[0], int2[0])
    end = min(int1[1], int2[1])
    if start < end:
        return (start, end)
    else:
        return None

patricia_busy = {
    'Monday': [
        (10*60, 10*60 + 30),
        (11*60 + 30, 12*60),
        (13*60, 13*60 + 30),
        (14*60 + 30, 15*60 + 30),
        (16*60, 16*60 + 30)
    ],
    'Tuesday': [
        (10*60, 10*60 + 30),
        (11*60, 12*60),
        (14*60, 16*60),
        (16*60 + 30, 17*60)
    ]
}

jesse_busy = {
    'Monday': [
        (9*60, 17*60)
    ],
    'Tuesday': [
        (11*60, 11*60 + 30),
        (12*60, 12*60 + 30),
        (13*60, 14*60),
        (14*60 + 30, 15*60),
        (15*60 + 30, 17*60)
    ]
}

for day in ['Monday', 'Tuesday']:
    p_buses = patricia_busy.get(day, [])
    j_buses = jesse_busy.get(day, [])
    p_free = get_free_intervals(p_buses, 9*60, 17*60)
    j_free = get_free_intervals(j_buses, 9*60, 17*60)
    for p_start, p_end in p_free:
        for j_start, j_end in j_free:
            overlap = interval_intersection((p_start, p_end), (j_start, j_end))
            if overlap:
                overlap_start, overlap_end = overlap
                if overlap_end - overlap_start >= 60:
                    start_time = f"{overlap_start // 60:02d}:{overlap_start % 60:02d}"
                    end_time = f"{overlap_end // 60:02d}:{overlap_end % 60:02d}"
                    print(f"{start_time}:{end_time} {day}")
                    exit()