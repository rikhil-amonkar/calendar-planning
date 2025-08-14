def get_free_intervals(work_start, work_end, busy_intervals):
    busy_intervals.sort()
    free = []
    current = work_start
    for start, end in busy_intervals:
        if current < start:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def find_overlaps(intervals1, intervals2):
    overlaps = []
    i = j = 0
    while i < len(intervals1) and j < len(intervals2):
        s1, e1 = intervals1[i]
        s2, e2 = intervals2[j]
        start = max(s1, s2)
        end = min(e1, e2)
        if start < end:
            overlaps.append((start, end))
        if e1 < e2:
            i += 1
        else:
            j += 1
    return overlaps

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_priority(day, start):
    if day == 'Monday':
        if start >= 12 * 60:  # 12:00 is 720 minutes
            return 1
        else:
            return 2
    elif day == 'Wednesday':
        return 3
    else:  # Tuesday, but no candidates there
        return 4

# Work hours
work_start = 9 * 60
work_end = 17 * 60

# Busy times for participants
joshua_busy = {
    'Monday': [(15 * 60, 15 * 60 + 30)],  # 15:00-15:30
    'Tuesday': [(11 * 60 + 30, 12 * 60), (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 15 * 60)],
    'Wednesday': []
}

joyce_busy = {
    'Monday': [
        (9 * 60, 9 * 60 + 30),  # 9:00-9:30
        (10 * 60, 11 * 60),    # 10:00-11:00
        (11 * 60 + 30, 12 * 60 + 30),  # 11:30-12:30
        (13 * 60, 15 * 60),    # 13:00-15:00
        (15 * 60 + 30, 17 * 60) # 15:30-17:00
    ],
    'Tuesday': [(9 * 60, 17 * 60)],  # all day
    'Wednesday': [
        (9 * 60, 9 * 60 + 30),  # 9:00-9:30
        (10 * 60, 11 * 60),     # 10:00-11:00
        (12 * 60 + 30, 15 * 60 + 30),  # 12:30-15:30
        (16 * 60, 16 * 60 + 30) # 16:00-16:30
    ]
}

candidates = []

for day in ['Monday', 'Tuesday', 'Wednesday']:
    # Get free intervals for Joshua and Joyce
    joshua_free = get_free_intervals(work_start, work_end, joshua_busy.get(day, []))
    joyce_free = get_free_intervals(work_start, work_end, joyce_busy.get(day, []))
    
    overlaps = find_overlaps(joshua_free, joyce_free)
    
    for start, end in overlaps:
        duration = end - start
        if duration >= 30:  # in minutes
            candidates.append((day, start, end))

# Sort candidates by priority
candidates.sort(key=lambda x: get_priority(x[0], x[1]))

# Select the first candidate
best_day, best_start, best_end = candidates[0]

# Format output
time_str = f"{minutes_to_time(best_start)}:{minutes_to_time(best_end)}"
print(f"{time_str} {best_day}")