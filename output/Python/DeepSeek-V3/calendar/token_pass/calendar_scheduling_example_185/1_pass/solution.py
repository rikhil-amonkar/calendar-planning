def time_to_min(t):
    # t is "HH:MM"
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def schedule_meeting(busy_times, work_start, work_end, duration, avoid_before):
    # busy_times: list of list of (start_min, end_min) for each person
    # work_start, work_end in "HH:MM"
    # avoid_before in "HH:MM"
    work_start_min = time_to_min(work_start)
    work_end_min = time_to_min(work_end)
    avoid_before_min = time_to_min(avoid_before)
    
    # Flatten and merge all busy intervals
    all_busy = []
    for person in busy_times:
        all_busy.extend(person)
    
    # Sort by start time
    all_busy.sort(key=lambda x: x[0])
    
    # Merge intervals
    merged = []
    for start, end in all_busy:
        if not merged or merged[-1][1] < start:
            merged.append([start, end])
        else:
            merged[-1][1] = max(merged[-1][1], end)
    
    # Find free slots within work hours
    free_slots = []
    prev_end = work_start_min
    for start, end in merged:
        if start > prev_end:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end_min:
        free_slots.append((prev_end, work_end_min))
    
    # Filter slots with enough duration and after avoid_before
    for start, end in free_slots:
        slot_start = max(start, avoid_before_min)
        if end - slot_start >= duration:
            return slot_start, slot_start + duration
    
    return None

# Define busy times in minutes from 9:00
# 9:00 = 0 min
kimberly = [(60, 90), (120, 180), (420, 450)]
marie = [(60, 120), (150, 360), (420, 450)]
diana = [(30, 60), (90, 330), (390, 480)]
megan = []  # no meetings

busy_times = [kimberly, marie, diana, megan]

work_start = "9:00"
work_end = "17:00"
duration = 30  # minutes
avoid_before = "10:00"  # Megan's preference

result = schedule_meeting(busy_times, work_start, work_end, duration, avoid_before)

if result:
    start_min, end_min = result
    start_time = min_to_time(start_min)
    end_time = min_to_time(end_min)
    print(f"Monday {start_time}:{end_time}")
else:
    print("No suitable slot found")