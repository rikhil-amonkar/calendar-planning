def get_free_intervals(busy_intervals, day_start=9, day_end=17):
    busy_sorted = sorted(busy_intervals, key=lambda x: x[0])
    free = [(day_start, day_end)]
    for start, end in busy_sorted:
        new_free = []
        for (f_start, f_end) in free:
            if end <= f_start:
                new_free.append((f_start, f_end))
            elif start >= f_end:
                new_free.append((f_start, f_end))
            else:
                if f_start < start:
                    new_free.append((f_start, start))
                if f_end > end:
                    new_free.append((end, f_end))
        free = new_free
    return free

nancy_schedule = {
    'Monday': [(10, 10.5), (11.5, 12.5), (13.5, 14), (14.5, 15.5), (16, 17)],
    'Tuesday': [(9.5, 10.5), (11, 11.5), (12, 12.5), (13, 13.5), (15.5, 16)],
    'Wednesday': [(10, 11.5), (13.5, 16)],
}

jose_schedule = {
    'Monday': [(9, 17)],
    'Tuesday': [(9, 17)],
    'Wednesday': [(9, 9.5), (10, 12.5), (13.5, 14.5), (15, 17)],
}

candidates = []
days = ['Monday', 'Tuesday', 'Wednesday']

for day in days:
    n_busy = nancy_schedule.get(day, [])
    j_busy = jose_schedule.get(day, [])
    n_free = get_free_intervals(n_busy)
    j_free = get_free_intervals(j_busy)
    for n_start, n_end in n_free:
        for j_start, j_end in j_free:
            overlap_start = max(n_start, j_start)
            overlap_end = min(n_end, j_end)
            duration = overlap_end - overlap_start
            if duration >= 0.5:  # 30 minutes
                candidates.append((overlap_start, overlap_end, day))

if candidates:
    earliest = min(candidates, key=lambda x: x[0])
    start_time = earliest[0]
    end_time = earliest[1]
    day = earliest[2]
    
    def float_to_time(f):
        hours = int(f)
        mins = int((f - hours) * 60)
        return f"{hours:02d}:{mins:02d}"
    
    start_str = float_to_time(start_time)
    end_str = float_to_time(end_time)
    time_range = f"{start_str}:{end_str}"
    print(f"{time_range} {day}")