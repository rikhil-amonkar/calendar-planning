work_start = 9 * 60
work_end = 17 * 60
meeting_duration = 30  # minutes

adam_busy = [
    (9 * 60 + 30, 10 * 60),
    (12 * 60 + 30, 13 * 60),
    (14 * 60 + 30, 15 * 60),
    (16 * 60 + 30, 17 * 60)
]

roy_busy = [
    (10 * 60, 11 * 60),
    (11 * 60 + 30, 13 * 60),
    (13 * 60 + 30, 14 * 60 + 30),
    (16 * 60 + 30, 17 * 60)
]


def get_free_slots(busy_times, work_start, work_end):
    busy_times_sorted = sorted(busy_times, key=lambda x: x[0])
    free_slots = []
    prev_end = work_start
    for start, end in busy_times_sorted:
        if start > prev_end:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_slots.append((prev_end, work_end))
    return free_slots


adam_free = get_free_slots(adam_busy, work_start, work_end)
roy_free = get_free_slots(roy_busy, work_start, work_end)

common_slots = []
for a_start, a_end in adam_free:
    for r_start, r_end in roy_free:
        start = max(a_start, r_start)
        end = min(a_end, r_end)
        if end - start >= meeting_duration:
            common_slots.append((start, end))

common_slots.sort()
earliest_start, earliest_end = common_slots[0]


def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"


time_range = f"{minutes_to_time_str(earliest_start)}:{minutes_to_time_str(earliest_end)}"
day = "Monday"
print(f"{time_range} {day}")