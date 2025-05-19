def time_to_minutes(t):
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = [sorted_intervals[0]]
    for current in sorted_intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

busy_intervals = []

cynthia_busy = [
    ("09:30", "10:30"),
    ("11:30", "12:00"),
    ("13:00", "13:30"),
    ("15:00", "16:00")
]
for start, end in cynthia_busy:
    busy_intervals.append((time_to_minutes(start), time_to_minutes(end)))

lauren_busy = [
    ("09:00", "09:30"),
    ("10:30", "11:00"),
    ("11:30", "12:00"),
    ("13:00", "13:30"),
    ("14:00", "14:30"),
    ("15:00", "15:30"),
    ("16:00", "17:00")
]
for start, end in lauren_busy:
    busy_intervals.append((time_to_minutes(start), time_to_minutes(end)))

robert_busy = [
    ("10:30", "11:00"),
    ("11:30", "12:00"),
    ("12:30", "13:30"),
    ("14:00", "16:00")
]
for start, end in robert_busy:
    busy_intervals.append((time_to_minutes(start), time_to_minutes(end)))

merged_busy = merge_intervals(busy_intervals)

free_intervals = []
previous_end = work_start
for start, end in merged_busy:
    if start > previous_end:
        free_intervals.append((previous_end, start))
    previous_end = max(previous_end, end)
if previous_end < work_end:
    free_intervals.append((previous_end, work_end))

meeting_duration = 30
for start, end in free_intervals:
    if end - start >= meeting_duration:
        meeting_start = start
        meeting_end = meeting_start + meeting_duration
        start_time = minutes_to_time(meeting_start)
        end_time = minutes_to_time(meeting_end)
        print(f"Monday:{start_time}:{end_time}")
        break