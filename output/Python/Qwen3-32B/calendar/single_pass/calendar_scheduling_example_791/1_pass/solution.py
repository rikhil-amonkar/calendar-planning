def adjust_ruth_wednesday(busy_intervals):
    work_end = 13 * 60 + 30  # 810 minutes
    adjusted = []
    for start, end in busy_intervals:
        if start >= work_end:
            continue
        new_end = min(end, work_end)
        adjusted.append((start, new_end))
    return adjusted

def get_free_intervals(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    merged = []
    for interval in sorted_busy:
        if not merged:
            merged.append(interval)
        else:
            last_start, last_end = merged[-1]
            curr_start, curr_end = interval
            if curr_start <= last_end:
                merged[-1] = (last_start, max(last_end, curr_end))
            else:
                merged.append(interval)
    free = []
    prev_end = work_start
    for start, end in merged:
        if prev_end < start:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def interval_overlap(a_start, a_end, b_start, b_end):
    latest_start = max(a_start, b_start)
    earliest_end = min(a_end, b_end)
    if latest_start < earliest_end:
        return (latest_start, earliest_end)
    else:
        return None

def find_meeting_time():
    nicole_schedule = {
        'Monday': [(540, 570), (780, 810), (870, 930)],
        'Tuesday': [(540, 570), (750, 810), (870, 930)],
        'Wednesday': [(600, 660), (750, 900), (960, 1020)],
    }
    ruth_original_schedule = {
        'Monday': [(540, 1020)],
        'Tuesday': [(540, 1020)],
        'Wednesday': [(540, 630), (660, 690), (720, 750), (810, 930), (960, 990)],
    }
    days = ['Monday', 'Tuesday', 'Wednesday']
    for day in days:
        if day not in nicole_schedule or day not in ruth_original_schedule:
            continue
        nicole_busy = nicole_schedule[day]
        if day == 'Wednesday':
            ruth_busy = adjust_ruth_wednesday(ruth_original_schedule[day])
            ruth_work_end = 13 * 60 + 30  # 810
        else:
            ruth_busy = ruth_original_schedule[day]
            ruth_work_end = 1020
        nicole_free = get_free_intervals(nicole_busy, 540, 1020)
        ruth_free = get_free_intervals(ruth_busy, 540, ruth_work_end)
        for n_start, n_end in nicole_free:
            for r_start, r_end in ruth_free:
                overlap = interval_overlap(n_start, n_end, r_start, r_end)
                if overlap:
                    start, end = overlap
                    if end - start >= 30:
                        start_time = f"{start//60:02d}:{start%60:02d}"
                        end_time = f"{end//60:02d}:{end%60:02d}"
                        print(f"{start_time}:{end_time} Wednesday")
                        return

find_meeting_time()