def min_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

work_start = 9 * 60
work_end = 17 * 60
busy_times = [(9 * 60, 10 * 60), (10 * 60 + 30, 16 * 60 + 30)]
meeting_duration = 30
preferred_start_min = 16 * 60

free_slots = []
current = work_start
busy_sorted = sorted(busy_times, key=lambda x: x[0])
for start_busy, end_busy in busy_sorted:
    if current < start_busy:
        free_slots.append((current, start_busy))
    current = max(current, end_busy)
if current < work_end:
    free_slots.append((current, work_end))

meeting_start = None
meeting_end = None
for start, end in free_slots:
    if (end - start) >= meeting_duration and start >= preferred_start_min:
        meeting_start = start
        meeting_end = start + meeting_duration
        break

start_str = min_to_time(meeting_start)
end_str = min_to_time(meeting_end)
time_range_str = f"{start_str}:{end_str}"

print("Monday")
print(time_range_str)