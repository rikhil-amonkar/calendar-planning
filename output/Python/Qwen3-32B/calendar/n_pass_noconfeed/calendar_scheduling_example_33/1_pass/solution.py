def to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(work_start, work_end, busy_intervals):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current_start = work_start
    for start, end in sorted_busy:
        if current_start < start:
            free.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < work_end:
        free.append((current_start, work_end))
    return free

def is_free(free_intervals, start, end):
    for fs, fe in free_intervals:
        if start >= fs and end <= fe:
            return True
    return False

work_start = 9 * 60  # 540 minutes
work_end = 17 * 60   # 1020 minutes

# Lisa's busy times
busy_lisa = [
    (9*60, 10*60),
    (10*60 + 30, 11*60 + 30),
    (12*60 + 30, 13*60),
    (16*60, 16*60 + 30)
]

# Bobby's busy times
busy_bobby = [
    (9*60, 9*60 + 30),
    (10*60, 10*60 + 30),
    (11*60 + 30, 12*60),
    (15*60, 15*60 + 30)
]

# Randy's busy times
busy_randy = [
    (9*60 + 30, 10*60),
    (10*60 + 30, 11*60),
    (11*60 + 30, 12*60 + 30),
    (13*60, 13*60 + 30),
    (14*60 + 30, 15*60 + 30),
    (16*60, 16*60 + 30)
]

# Compute free intervals
free_lisa = get_free_intervals(work_start, work_end, busy_lisa)
free_bobby = get_free_intervals(work_start, work_end, busy_bobby)
free_randy = get_free_intervals(work_start, work_end, busy_randy)

meeting_duration = 30
bobby_end_limit = 15 * 60  # 900 minutes

for start in range(work_start, bobby_end_limit - meeting_duration + 1):
    end = start + meeting_duration
    if (is_free(free_lisa, start, end) and
        is_free(free_bobby, start, end) and
        is_free(free_randy, start, end)):
        start_time = to_time_str(start)
        end_time = to_time_str(end)
        print(f"{start_time}:{end_time} Monday")
        break