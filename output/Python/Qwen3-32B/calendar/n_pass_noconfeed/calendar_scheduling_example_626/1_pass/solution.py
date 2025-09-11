def get_free_intervals(busy_intervals, work_start, work_end):
    if not busy_intervals:
        return [(work_start, work_end)] if work_start < work_end else []
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

def minutes_to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours:02d}:{minutes:02d}"

work_start = 9 * 60  # 540 minutes
work_end = 17 * 60   # 1020 minutes

# Define busy times for each day and person
# Monday
patricia_mon = [
    (10*60, 10*60 + 30),  # 10:00-10:30
    (11*60 + 30, 12*60),  # 11:30-12:00
    (13*60, 13*60 + 30),  # 13:00-13:30
    (14*60 + 30, 15*60 + 30),  # 14:30-15:30
    (16*60, 16*60 + 30)  # 16:00-16:30
]
jesse_mon = [
    (9*60, 17*60)  # 9:00-17:00
]

# Tuesday
patricia_tue = [
    (10*60, 10*60 + 30),  # 10:00-10:30
    (11*60, 12*60),  # 11:00-12:00
    (14*60, 16*60),  # 14:00-16:00
    (16*60 + 30, 17*60)  # 16:30-17:00
]
jesse_tue = [
    (11*60, 11*60 + 30),  # 11:00-11:30
    (12*60, 12*60 + 30),  # 12:00-12:30
    (13*60, 14*60),  # 13:00-14:00
    (14*60 + 30, 15*60),  # 14:30-15:00
    (15*60 + 30, 17*60)  # 15:30-17:00
]

days = ['Monday', 'Tuesday']

for day in days:
    if day == 'Monday':
        p_busy = patricia_mon
        j_busy = jesse_mon
    else:  # Tuesday
        p_busy = patricia_tue
        j_busy = jesse_tue

    p_free = get_free_intervals(p_busy, work_start, work_end)
    j_free = get_free_intervals(j_busy, work_start, work_end)

    # Check for overlapping intervals
    for p_start, p_end in p_free:
        for j_start, j_end in j_free:
            overlap_start = max(p_start, j_start)
            overlap_end = min(p_end, j_end)
            if overlap_start < overlap_end:
                duration = overlap_end - overlap_start
                if duration >= 60:  # 1 hour
                    start_time = minutes_to_time(overlap_start)
                    end_time = minutes_to_time(overlap_end)
                    print(f"{start_time}:{end_time} {day}")
                    exit()