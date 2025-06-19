def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def compute_free_intervals(busy_intervals, work_start, work_end):
    if not busy_intervals:
        return [[work_start, work_end]]
    busy_sorted = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current = work_start
    for interval in busy_sorted:
        s, e = interval
        if current < s:
            free.append([current, s])
        current = max(current, e)
    if current < work_end:
        free.append([current, work_end])
    return free

def intersect_intervals(intervals1, intervals2):
    if not intervals1 or not intervals2:
        return []
    i = j = 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        a_start, a_end = intervals1[i]
        b_start, b_end = intervals2[j]
        low = max(a_start, b_start)
        high = min(a_end, b_end)
        if low < high:
            result.append([low, high])
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return result

work_start = time_str_to_minutes("9:00")
work_end = time_str_to_minutes("17:00")
duration = 30

participants_busy = {
    'Walter': [],
    'Cynthia': [["9:00", "9:30"], ["10:00", "10:30"], ["13:30", "14:30"], ["15:00", "16:00"]],
    'Ann': [["10:00", "11:00"], ["13:00", "13:30"], ["14:00", "15:00"], ["16:00", "16:30"]],
    'Catherine': [["9:00", "11:30"], ["12:30", "13:30"], ["14:30", "17:00"]],
    'Kyle': [["9:00", "9:30"], ["10:00", "11:30"], ["12:00", "12:30"], ["13:00", "14:30"], ["15:00", "16:00"]]
}

free_intervals_list = []
for person, busy_list in participants_busy.items():
    busy_minutes = []
    for interval in busy_list:
        start_min = time_str_to_minutes(interval[0])
        end_min = time_str_to_minutes(interval[1])
        busy_minutes.append([start_min, end_min])
    free_intervals = compute_free_intervals(busy_minutes, work_start, work_end)
    free_intervals_list.append(free_intervals)

common = free_intervals_list[0]
for i in range(1, len(free_intervals_list)):
    common = intersect_intervals(common, free_intervals_list[i])

meeting_start = None
for interval in common:
    start, end = interval
    if end - start >= duration:
        meeting_start = start
        break

if meeting_start is None:
    print("No suitable time found")
else:
    meeting_end = meeting_start + duration
    start_hour = meeting_start // 60
    start_minute = meeting_start % 60
    end_hour = meeting_end // 60
    end_minute = meeting_end % 60
    time_str = f"{start_hour}:{start_minute:02d}:{end_hour}:{end_minute:02d}"
    print("Monday")
    print(time_str)