def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for current in intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def find_earliest_meeting(busy_intervals, work_start, work_end, duration):
    free_intervals = []
    current_start = work_start
    
    for start, end in busy_intervals:
        if current_start < start:
            free_intervals.append((current_start, start))
        current_start = max(current_start, end)
    
    if current_start < work_end:
        free_intervals.append((current_start, work_end))
    
    for start, end in free_intervals:
        if end - start >= duration:
            meeting_start = start
            meeting_end = meeting_start + duration
            return (meeting_start, meeting_end)
    return None

# Parameters
work_start_min = time_to_minutes("9:00")
work_end_min = time_to_minutes("17:00")
duration_min = 30  # 30 minutes

# Adam's busy intervals
adam_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Roy's busy intervals
roy_busy = [
    (time_to_minutes("10:00"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("13:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:30")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Combine and merge busy intervals
all_busy = adam_busy + roy_busy
merged_busy = merge_intervals(all_busy)

# Find earliest meeting slot
meeting_slot = find_earliest_meeting(merged_busy, work_start_min, work_end_min, duration_min)

if meeting_slot:
    start_min, end_min = meeting_slot
    start_time = minutes_to_time(start_min)
    end_time = minutes_to_time(end_min)
    print(f"Monday:{start_time}:{end_time}")
else:
    print("No suitable slot found")