def time_to_min(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    intervals.sort(key=lambda x: x[0])
    merged = []
    for start, end in intervals:
        if not merged or merged[-1][1] < start:
            merged.append([start, end])
        else:
            merged[-1][1] = max(merged[-1][1], end)
    return merged

def find_meeting_slot(busy1, busy2, work_start, work_end, meeting_duration, extra_constraint_end=None):
    # Convert to minutes
    work_start_min = time_to_min(work_start)
    work_end_min = time_to_min(work_end)
    if extra_constraint_end:
        extra_end_min = time_to_min(extra_constraint_end)
        work_end_min = min(work_end_min, extra_end_min)
    
    # Combine busy intervals
    all_busy = busy1 + busy2
    for i in range(len(all_busy)):
        all_busy[i] = [time_to_min(all_busy[i][0]), time_to_min(all_busy[i][1])]
    
    merged_busy = merge_intervals(all_busy)
    
    # Check gaps between work_start and work_end
    possible_slots = []
    current_time = work_start_min
    
    for start_busy, end_busy in merged_busy:
        if current_time < start_busy:
            gap = start_busy - current_time
            if gap >= meeting_duration:
                possible_slots.append((current_time, start_busy))
        current_time = max(current_time, end_busy)
    
    # After last busy interval
    if current_time < work_end_min:
        gap = work_end_min - current_time
        if gap >= meeting_duration:
            possible_slots.append((current_time, work_end_min))
    
    # Filter slots to ensure they end by extra_constraint_end if given
    if extra_constraint_end:
        filtered = []
        for s, e in possible_slots:
            if s + meeting_duration <= extra_end_min:
                filtered.append((s, e))
        possible_slots = filtered
    
    return possible_slots

# Define busy times as (start, end) strings
jesse_busy = [
    ("13:30", "14:00"),
    ("14:30", "15:00"),
    ("09:00", "09:30"),
    ("13:00", "13:30"),
    ("14:00", "15:00")
]

lawrence_busy = [
    ("09:00", "17:00"),  # Monday full day
    ("09:30", "10:30"),
    ("11:30", "12:30"),
    ("13:00", "13:30"),
    ("14:30", "15:00"),
    ("15:30", "16:30")
]

# Monday: Lawrence busy all day → no slot
# Tuesday: Use only Tuesday busy for Lawrence (ignore Monday entry for Tuesday calculation)
lawrence_tuesday_busy = [
    ("09:30", "10:30"),
    ("11:30", "12:30"),
    ("13:00", "13:30"),
    ("14:30", "15:00"),
    ("15:30", "16:30")
]

work_start = "09:00"
work_end = "17:00"
meeting_duration = 30  # minutes
extra_constraint_end = "16:30"  # Lawrence cannot meet after 16:30

slots = find_meeting_slot(jesse_busy, lawrence_tuesday_busy, work_start, work_end, meeting_duration, extra_constraint_end)

if slots:
    # Pick earliest slot
    start_min = slots[0][0]
    end_meeting = start_min + meeting_duration
    day = "Tuesday"
    print(f"{day} {min_to_time(start_min)}:{min_to_time(end_meeting)}")
else:
    print("No suitable slot found")