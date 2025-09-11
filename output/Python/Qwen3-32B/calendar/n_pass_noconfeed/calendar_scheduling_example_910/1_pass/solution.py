def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, work_start=540, work_end=1020):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    prev_end = work_start
    for start, end in sorted_busy:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

# Bryan's busy times per day
bryan_busy = {
    'Monday': [],
    'Tuesday': [],
    'Wednesday': [],
    'Thursday': [(9*60+30, 9*60+60), (12*60+30, 13*60+0)],
    'Friday': [(10*60+30, 11*60+0), (14*60+0, 14*60+30)],
}

# Nicholas's busy times per day
nicholas_busy = {
    'Monday': [(11*60+30, 12*60+0), (13*60+0, 15*60+30)],
    'Tuesday': [(9*60+0, 9*60+30), (11*60+0, 13*60+30), (14*60+0, 16*60+30)],
    'Wednesday': [(9*60+0, 9*60+30), (10*60+0, 11*60+0), (11*60+30, 13*60+30), (14*60+0, 14*60+30), (15*60+0, 16*60+30)],
    'Thursday': [(10*60+30, 11*60+30), (12*60+0, 12*60+30), (15*60+0, 15*60+30), (16*60+30, 17*60+0)],
    'Friday': [(9*60+0, 10*60+30), (11*60+0, 12*60+0), (12*60+30, 14*60+30), (15*60+30, 16*60+0), (16*60+30, 17*60+0)],
}

days_to_check = ['Wednesday', 'Friday', 'Tuesday']

for day in days_to_check:
    bryan_day_busy = bryan_busy.get(day, [])
    nicholas_day_busy = nicholas_busy.get(day, [])
    
    bryan_free = get_free_intervals(bryan_day_busy)
    nicholas_free = get_free_intervals(nicholas_day_busy)
    
    for b_start, b_end in bryan_free:
        for n_start, n_end in nicholas_free:
            overlap_start = max(b_start, n_start)
            overlap_end = min(b_end, n_end)
            if overlap_start < overlap_end:
                duration = overlap_end - overlap_start
                if duration >= 60:
                    start_time = minutes_to_time(overlap_start)
                    end_time = minutes_to_time(overlap_start + 60)
                    print(f"{day} {start_time}:{end_time}")
                    exit()