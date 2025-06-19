work_start = 540  # 9:00 in minutes from midnight
work_end = 1020   # 17:00

harold_busy = {
    "Monday": [(540, 600), (630, 1020)],
    "Tuesday": [(540, 570), (630, 690), (750, 810), (870, 930), (960, 1020)]
}

meeting_duration = 30

days = ["Monday", "Tuesday"]
free_intervals = {}

for day in days:
    busy_list = harold_busy[day]
    busy_list.sort(key=lambda x: x[0])
    free = []
    current = work_start
    for interval in busy_list:
        s, e = interval
        if current < s:
            free.append((current, s))
        current = e
    if current < work_end:
        free.append((current, work_end))
    free_intervals[day] = free

candidate_day = None
candidate_slot = None

for interval in free_intervals["Tuesday"]:
    start, end = interval
    if end - start >= meeting_duration:
        if start >= 870:
            if start + meeting_duration <= end:
                candidate_day = "Tuesday"
                candidate_slot = (start, start + meeting_duration)
                break

if candidate_day is None:
    for interval in free_intervals["Tuesday"]:
        start, end = interval
        if end - start >= meeting_duration:
            if start + meeting_duration <= end:
                candidate_day = "Tuesday"
                candidate_slot = (start, start + meeting_duration)
                break

if candidate_day is None:
    for interval in free_intervals["Monday"]:
        start, end = interval
        if end - start >= meeting_duration:
            if start + meeting_duration <= end:
                candidate_day = "Monday"
                candidate_slot = (start, start + meeting_duration)
                break

start_min, end_min = candidate_slot
start_hour = start_min // 60
start_minute = start_min % 60
end_hour = end_min // 60
end_minute = end_min % 60
time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"

print(candidate_day)
print(time_str)