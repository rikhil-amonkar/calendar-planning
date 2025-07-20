def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

work_start = time_to_minutes("9:00")
work_end = time_to_minutes("17:00")
meeting_duration = 60

kayla_busy = [
    ("10:00", "10:30"),
    ("14:30", "16:00")
]

rebecca_busy = [
    ("9:00", "13:00"),
    ("13:30", "15:00"),
    ("15:30", "16:00")
]

def get_free_intervals(busy_intervals, work_start, work_end):
    busy_minutes = []
    for start, end in busy_intervals:
        s_min = time_to_minutes(start)
        e_min = time_to_minutes(end)
        busy_minutes.append((s_min, e_min))
    
    busy_minutes.sort()
    
    free_intervals = []
    current = work_start
    
    for start, end in busy_minutes:
        if current < start:
            free_intervals.append((current, start))
        current = max(current, end)
    
    if current < work_end:
        free_intervals.append((current, work_end))
    
    return free_intervals

kayla_free = get_free_intervals(kayla_busy, work_start, work_end)
rebecca_free = get_free_intervals(rebecca_busy, work_start, work_end)

found_slot = None
for k_start, k_end in kayla_free:
    for r_start, r_end in rebecca_free:
        overlap_start = max(k_start, r_start)
        overlap_end = min(k_end, r_end)
        if overlap_start < overlap_end and (overlap_end - overlap_start) >= meeting_duration:
            found_slot = (overlap_start, overlap_start + meeting_duration)
            break
    if found_slot:
        break

if found_slot:
    start_time = minutes_to_time(found_slot[0])
    end_time = minutes_to_time(found_slot[1])
    print(f"Monday {start_time}:{end_time}")
else:
    print("No suitable slot found")