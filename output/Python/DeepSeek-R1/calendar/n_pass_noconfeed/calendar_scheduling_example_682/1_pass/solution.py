def time_to_minutes(time_str):
    hours, minutes = time_str.split(':')
    return int(hours) * 60 + int(minutes)

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Work hours and constraints for Tuesday (only day considered due to Nathan's constraint)
work_start = time_to_minutes('9:00')  # 540 minutes
work_end = time_to_minutes('11:00')   # 660 minutes (Amanda doesn't want to meet after 11:00)

# Amanda's busy intervals on Tuesday (before 11:00)
amanda_busy = [
    ('9:00', '9:30'),
    ('10:00', '10:30')
]
amanda_busy_minutes = [(time_to_minutes(s), time_to_minutes(e)) for s, e in amanda_busy]

# Nathan's busy intervals on Tuesday (before 11:00)
nathan_busy = [
    ('9:00', '10:30')
]
nathan_busy_minutes = [(time_to_minutes(s), time_to_minutes(e)) for s, e in nathan_busy]

def find_free_intervals(busy_intervals, start_bound, end_bound):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current = start_bound
    for start, end in sorted_busy:
        if current < start:
            free.append((current, start))
        current = max(current, end)
    if current < end_bound:
        free.append((current, end_bound))
    return free

amanda_free = find_free_intervals(amanda_busy_minutes, work_start, work_end)
nathan_free = find_free_intervals(nathan_busy_minutes, work_start, work_end)

meeting_duration = 30  # minutes
found_interval = None

for a_start, a_end in amanda_free:
    for n_start, n_end in nathan_free:
        overlap_start = max(a_start, n_start)
        overlap_end = min(a_end, n_end)
        if overlap_end - overlap_start >= meeting_duration:
            found_interval = (overlap_start, overlap_start + meeting_duration)
            break
    if found_interval:
        break

if found_interval:
    start_min, end_min = found_interval
    start_time = minutes_to_time(start_min)
    end_time = minutes_to_time(end_min)
    time_range_str = f"{start_time}:{end_time}"
    print("Tuesday")
    print(time_range_str)
else:
    print("No solution found")