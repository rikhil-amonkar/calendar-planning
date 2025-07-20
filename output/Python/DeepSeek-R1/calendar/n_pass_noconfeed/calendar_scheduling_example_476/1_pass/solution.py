def time_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Given constraints
work_start = time_to_minutes("12:30")  # 750 minutes (12:30)
work_end = time_to_minutes("17:00")    # 1020 minutes (17:00)
total_minutes = work_end - work_start   # 270 minutes

# Participants and their busy intervals (as time strings)
participants_busy = {
    "Daniel": [],
    "Kathleen": [("14:30", "15:30")],
    "Carolyn": [("13:00", "13:30")],  # Ignored 12:00-12:30 as it ends at work_start
    "Roger": [],
    "Cheryl": [("12:30", "13:30"), ("14:00", "17:00")],
    "Virginia": [("13:00", "13:30"), ("14:30", "15:30"), ("16:00", "17:00")],
    "Angela": [("13:00", "13:30"), ("14:00", "16:30")]
}

# Initialize free_all as all True for the entire period
free_all = [True] * total_minutes

for busy_list in participants_busy.values():
    free_p = [True] * total_minutes
    for (s_str, e_str) in busy_list:
        s = time_to_minutes(s_str)
        e = time_to_minutes(e_str)
        if s >= work_end or e <= work_start:
            continue
        busy_start = max(s, work_start)
        busy_end = min(e, work_end)
        if busy_start >= busy_end:
            continue
        start_idx = busy_start - work_start
        end_idx = busy_end - work_start
        for j in range(start_idx, end_idx):
            if j < total_minutes:
                free_p[j] = False
    for idx in range(total_minutes):
        free_all[idx] = free_all[idx] and free_p[idx]

# Search for the first 30 consecutive free minutes
n = 30
start_idx = None
for i in range(0, total_minutes - n + 1):
    if all(free_all[i:i + n]):
        start_idx = i
        break

if start_idx is None:
    print("No suitable time found")
else:
    start_minute = work_start + start_idx
    end_minute = start_minute + n
    start_time_str = minutes_to_time(start_minute)
    end_time_str = minutes_to_time(end_minute)
    time_range_str = f"{start_time_str}:{end_time_str}"
    print("Monday")
    print(time_range_str)