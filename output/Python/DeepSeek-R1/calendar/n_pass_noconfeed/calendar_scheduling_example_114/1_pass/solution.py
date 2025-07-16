def time_to_minutes(time_str):
    parts = time_str.split(':')
    h = int(parts[0])
    m = int(parts[1])
    return (h - 9) * 60 + m

def minutes_to_time(minutes):
    total_minutes = minutes
    h = 9 + total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def intersect_intervals(intervals1, intervals2):
    i = j = 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        low = max(intervals1[i][0], intervals2[j][0])
        high = min(intervals1[i][1], intervals2[j][1])
        if low < high:
            result.append((low, high))
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return result

busy_times = {
    "Stephanie": [("10:00", "10:30"), ("16:00", "16:30")],
    "Cheryl": [("10:00", "10:30"), ("11:30", "12:00"), ("13:30", "14:00"), ("16:30", "17:00")],
    "Bradley": [("9:30", "10:00"), ("10:30", "11:30"), ("13:30", "14:00"), ("14:30", "15:00"), ("15:30", "17:00")],
    "Steven": [("9:00", "12:00"), ("13:00", "13:30"), ("14:30", "17:00")]
}

busy_intervals = {}
for person, intervals in busy_times.items():
    busy_list = []
    for (start_str, end_str) in intervals:
        start_min = time_to_minutes(start_str)
        end_min = time_to_minutes(end_str)
        busy_list.append((start_min, end_min))
    busy_intervals[person] = busy_list

free_intervals = {}
for person, intervals in busy_intervals.items():
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    free_list = []
    current = 0
    for start, end in sorted_intervals:
        if current < start:
            free_list.append((current, start))
        current = end
    if current < 480:
        free_list.append((current, 480))
    free_intervals[person] = free_list

participants = list(busy_intervals.keys())
common_free = free_intervals[participants[0]]
for i in range(1, len(participants)):
    next_person = participants[i]
    next_free = free_intervals[next_person]
    common_free = intersect_intervals(common_free, next_free)

meeting_start = None
for start, end in common_free:
    if end - start >= 60:
        meeting_start = start
        break

if meeting_start is None:
    print("No solution found")
else:
    start_time_str = minutes_to_time(meeting_start)
    end_time_str = minutes_to_time(meeting_start + 60)
    print(f"Monday {start_time_str}:{end_time_str}")