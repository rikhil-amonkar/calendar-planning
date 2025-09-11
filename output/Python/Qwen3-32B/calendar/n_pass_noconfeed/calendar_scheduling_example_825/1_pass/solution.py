def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(work_start, work_end, busy_intervals):
    busy = sorted(busy_intervals)
    free = []
    prev_end = work_start
    for start, end in busy:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

laura_schedule = {
    'Monday': [(630, 660), (750, 780), (870, 930), (960, 1020)],
    'Tuesday': [(570, 600), (660, 690), (780, 810), (870, 900), (960, 1020)],
    'Wednesday': [(690, 720), (750, 780), (930, 990)],
    'Thursday': [(630, 660), (720, 810), (900, 930), (960, 990)],
}

philip_schedule = {
    'Monday': [(540, 1020)],
    'Tuesday': [(540, 660), (690, 720), (780, 810), (840, 870), (900, 990)],
    'Wednesday': [(540, 600), (660, 720), (750, 960), (990, 1020)],
    'Thursday': [(540, 630), (660, 750), (780, 1020)],
}

work_start = 540  # 9:00 AM
work_end = 1020   # 5:00 PM

days = ['Monday', 'Tuesday', 'Thursday']

for day in days:
    laura_buses = laura_schedule.get(day, [])
    philip_buses = philip_schedule.get(day, [])
    
    laura_free = get_free_intervals(work_start, work_end, laura_buses)
    philip_free = get_free_intervals(work_start, work_end, philip_buses)
    
    for l_start, l_end in laura_free:
        for p_start, p_end in philip_free:
            start_overlap = max(l_start, p_start)
            end_overlap = min(l_end, p_end)
            if start_overlap < end_overlap:
                duration = end_overlap - start_overlap
                if duration >= 60:
                    start_time = to_time_str(start_overlap)
                    end_time = to_time_str(end_overlap)
                    print(f"{day} {start_time}:{end_time}")
                    exit()