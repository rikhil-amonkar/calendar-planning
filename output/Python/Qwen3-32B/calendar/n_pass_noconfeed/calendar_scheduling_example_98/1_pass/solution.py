def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

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

def get_free_intervals(merged_buses, work_start, work_end):
    free = []
    prev_end = work_start
    for start, end in merged_buses:
        if prev_end < start:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

juan_buses = [
    (time_to_minutes("9:00"), time_to_minutes("10:30")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

marilyn_buses = [
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:00"))
]

ronald_buses = [
    (time_to_minutes("9:00"), time_to_minutes("10:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("16:30"))
]

all_buses = juan_buses + marilyn_buses + ronald_buses
merged = merge_intervals(all_buses)
work_start_minutes = time_to_minutes("9:00")
work_end_minutes = time_to_minutes("17:00")
meeting_end_limit = time_to_minutes("16:00")
meeting_duration = 30

free_intervals = get_free_intervals(merged, work_start_minutes, work_end_minutes)

found = False
for s, e in free_intervals:
    if e - s >= meeting_duration:
        meeting_end = s + meeting_duration
        if meeting_end <= meeting_end_limit:
            start_str = minutes_to_time(s)
            end_str = minutes_to_time(meeting_end)
            day = "Monday"
            print(f"{{{start_str}:{end_str}}}: {day}")
            found = True
            break

if not found:
    print("No suitable time found.")