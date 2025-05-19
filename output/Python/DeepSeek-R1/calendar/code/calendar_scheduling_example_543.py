def time_to_minutes(t):
    hours, mins = map(int, t.split(':'))
    return hours * 60 + mins

def minutes_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def compute_free_intervals(busy_intervals, work_start, work_end):
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

work_start = time_to_minutes("9:00")
work_end = time_to_minutes("17:00")

james_busy = [
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00"))
]

john_busy = [
    (time_to_minutes("9:30"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("16:30"))
]

james_free = compute_free_intervals(james_busy, work_start, work_end)
john_free = compute_free_intervals(john_busy, work_start, work_end)

overlapping = []
for j_start, j_end in james_free:
    for jo_start, jo_end in john_free:
        start = max(j_start, jo_start)
        end = min(j_end, jo_end)
        if start < end:
            overlapping.append((start, end))

meeting_duration = 60
proposed_time = None
for start, end in overlapping:
    if end - start >= meeting_duration:
        proposed_time = (start, start + meeting_duration)
        break

start_time = minutes_to_time(proposed_time[0])
end_time = minutes_to_time(proposed_time[1])
print(f"{start_time}:{end_time}")
print("Monday")