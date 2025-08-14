def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(work_start, work_end, busy_intervals):
    free = [(work_start, work_end)]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    for busy_start, busy_end in sorted_busy:
        new_free = []
        for interval_start, interval_end in free:
            if busy_end <= interval_start or busy_start >= interval_end:
                new_free.append((interval_start, interval_end))
            else:
                if interval_start < busy_start:
                    new_free.append((interval_start, busy_start))
                if busy_end < interval_end:
                    new_free.append((busy_end, interval_end))
        free = new_free
    return free

work_start = 9 * 60
work_end = 17 * 60

samuel_busy = [
    (9 * 60, 10 * 60 + 30),
    (11 * 60 + 30, 12 * 60),
    (13 * 60, 13 * 60 + 30),
    (14 * 60, 16 * 60),
    (16 * 60 + 30, 17 * 60)
]

free_intervals = get_free_intervals(work_start, work_end, samuel_busy)

meeting_duration = 30

for start, end in free_intervals:
    if end - start >= meeting_duration:
        meeting_start = start
        meeting_end = start + meeting_duration
        break

start_time = minutes_to_time(meeting_start)
end_time = minutes_to_time(meeting_end)
day = "Monday"

print(f"{start_time}:{end_time} {day}")