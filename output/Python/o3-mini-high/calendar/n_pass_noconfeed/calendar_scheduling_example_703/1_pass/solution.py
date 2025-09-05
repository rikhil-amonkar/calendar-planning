def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(work_start, work_end, busy_intervals):
    free = []
    current = work_start
    for start, end in busy_intervals:
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        start = max(start1, start2)
        end = min(end1, end2)
        if start + meeting_duration <= end:
            result.append((start, end))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

# Meeting duration in minutes
meeting_duration = 60

# Define work hours for each day
work_hours = {
    "Monday": ("09:00", "17:00"),
    "Tuesday": ("09:00", "17:00"),
    "Wednesday": ("09:00", "17:00")
}

# Busy schedules for Stephanie (times given in HH:MM format)
busy_stephanie = {
    "Monday": [("09:30", "10:00"), ("10:30", "11:00"), ("11:30", "12:00"), ("14:00", "14:30")],
    "Tuesday": [("12:00", "13:00")],
    "Wednesday": [("09:00", "10:00"), ("13:00", "14:00")]
}

# Busy schedules for Betty
busy_betty = {
    "Monday": [("09:00", "10:00"), ("11:00", "11:30"), ("14:30", "15:00"), ("15:30", "16:00")],
    "Tuesday": [("09:00", "09:30"), ("11:30", "12:00"), ("12:30", "14:30"), ("15:30", "16:00")],
    "Wednesday": [("10:00", "11:30"), ("12:00", "14:00"), ("14:30", "17:00")]
}

# Convert busy intervals to minutes
for day in busy_stephanie:
    busy_stephanie[day] = sorted([(time_to_minutes(s), time_to_minutes(e)) for s, e in busy_stephanie[day]])
for day in busy_betty:
    busy_betty[day] = sorted([(time_to_minutes(s), time_to_minutes(e)) for s, e in busy_betty[day]])

def get_candidate_slots(day):
    ws, we = work_hours[day]
    work_start = time_to_minutes(ws)
    work_end = time_to_minutes(we)
    
    free_steph = get_free_intervals(work_start, work_end, busy_stephanie.get(day, []))
    free_betty = get_free_intervals(work_start, work_end, busy_betty.get(day, []))
    
    # Get common free intervals
    common_free = intersect_intervals(free_steph, free_betty)
    candidates = []
    
    # For Tuesday, Betty cannot meet after 12:30 so candidate meeting must end by 12:30.
    latest_end_tuesday = time_to_minutes("12:30")
    
    for start, end in common_free:
        if end - start >= meeting_duration:
            candidate_start = start
            candidate_end = candidate_start + meeting_duration
            if day == "Tuesday" and candidate_end > latest_end_tuesday:
                # Try shifting the start so that meeting ends exactly at 12:30 if possible
                if latest_end_tuesday - meeting_duration >= start:
                    candidate_start = latest_end_tuesday - meeting_duration
                    candidate_end = latest_end_tuesday
                else:
                    continue
            # We found a candidate that fits in the interval.
            candidates.append((candidate_start, candidate_end))
    return candidates

# Preference: Stephanie would like to avoid Monday meetings; so try Tuesday first, then Wednesday, then Monday.
priority_days = ["Tuesday", "Wednesday", "Monday"]
meeting_slot = None
meeting_day = None

for day in priority_days:
    slots = get_candidate_slots(day)
    if slots:
        meeting_slot = slots[0]  # choose the earliest available slot of that day
        meeting_day = day
        break

if meeting_slot:
    start, end = meeting_slot
    time_range = f"{minutes_to_time(start)}:{minutes_to_time(end)}"
    print(f"{meeting_day}, {time_range}")
else:
    print("No available meeting slot found.")