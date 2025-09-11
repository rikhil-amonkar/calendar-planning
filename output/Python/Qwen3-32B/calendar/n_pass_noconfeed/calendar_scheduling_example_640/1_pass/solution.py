def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

def get_available_intervals(work_start, work_end, busy_intervals):
    busy_intervals.sort()
    available = []
    current = work_start
    for start, end in busy_intervals:
        if current < start:
            available.append((current, start))
        current = max(current, end)
    if current < work_end:
        available.append((current, work_end))
    return available

def find_overlaps(intervals1, intervals2):
    i = j = 0
    overlaps = []
    while i < len(intervals1) and j < len(intervals2):
        a_start, a_end = intervals1[i]
        b_start, b_end = intervals2[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            overlaps.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return overlaps

work_start = 9 * 60  # 540 minutes
work_end = 17 * 60   # 1020 minutes

# Define busy intervals for each day and person
days = ['Monday', 'Tuesday']
bobby_busy = {
    'Monday': [(14*60 + 30, 15*60)],  # 14:30-15:00
    'Tuesday': [
        (9*60, 11*60 + 30),  # 9:00-11:30
        (12*60, 12*60 + 30),  # 12:00-12:30
        (13*60, 15*60),  # 13:00-15:00
        (15*60 + 30, 17*60)  # 15:30-17:00
    ]
}
michael_busy = {
    'Monday': [
        (9*60, 10*60),  # 9:00-10:00
        (10*60 + 30, 13*60 + 30),  # 10:30-13:30
        (14*60, 15*60),  # 14:00-15:00
        (15*60 + 30, 17*60)  # 15:30-17:00
    ],
    'Tuesday': [
        (9*60, 10*60 + 30),  # 9:00-10:30
        (11*60, 11*60 + 30),  # 11:00-11:30
        (12*60, 14*60),  # 12:00-14:00
        (15*60, 16*60),  # 15:00-16:00
        (16*60 + 30, 17*60)  # 16:30-17:00
    ]
}

possible_slots = []

for day in days:
    # Get Bobby's busy intervals for the day
    bobby_intervals = bobby_busy.get(day, [])
    # Get Michael's busy intervals for the day
    michael_intervals = michael_busy.get(day, [])
    
    # Compute available intervals for Bobby
    bobby_available = get_available_intervals(work_start, work_end, bobby_intervals)
    # Compute available intervals for Michael
    michael_available = get_available_intervals(work_start, work_end, michael_intervals)
    
    # Find overlapping intervals
    overlaps = find_overlaps(bobby_available, michael_available)
    
    # Check each overlap for sufficient duration (>= 30 mins)
    for start, end in overlaps:
        duration = end - start
        if duration >= 30:
            possible_slots.append((day, start, end))

# Find the earliest possible slot
earliest_slot = min(possible_slots, key=lambda x: (days.index(x[0]), x[1]))

day_result = earliest_slot[0]
start_result = earliest_slot[1]
end_result = earliest_slot[1] + 30  # since the meeting is 30 minutes

start_time = minutes_to_time(start_result)
end_time = minutes_to_time(end_result)

print(f"{start_time}:{end_time} {day_result}")