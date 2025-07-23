def compute_free_intervals(busy_intervals, constraint):
    a, b = constraint
    intervals_in_constraint = []
    for start, end in busy_intervals:
        if end <= a or start >= b:
            continue
        s_clip = max(start, a)
        e_clip = min(end, b)
        intervals_in_constraint.append((s_clip, e_clip))
    
    if not intervals_in_constraint:
        return [(a, b)]
    
    intervals_in_constraint.sort(key=lambda x: x[0])
    free = []
    current = a
    for s, e in intervals_in_constraint:
        if current < s:
            free.append((current, s))
        current = max(current, e)
    if current < b:
        free.append((current, b))
    return free

def min_to_time(minutes):
    total_minutes = minutes
    hours = 9 + total_minutes // 60
    minutes_part = total_minutes % 60
    return f"{hours:02d}:{minutes_part:02d}"

day_constraints = {
    'Monday': (330, 480),
    'Tuesday': (0, 480)
}

schedules = {
    'Ryan': {
        'Monday': [
            (30, 60),    # 9:30-10:00
            (120, 180),  # 11:00-12:00
            (240, 270),  # 13:00-13:30
            (390, 420)   # 15:30-16:00
        ],
        'Tuesday': [
            (150, 210),  # 11:30-12:30
            (390, 420)   # 15:30-16:00
        ]
    },
    'Adam': {
        'Monday': [
            (0, 90),     # 9:00-10:30
            (120, 270),  # 11:00-13:30
            (300, 420),  # 14:00-16:00
            (450, 480)   # 16:30-17:00
        ],
        'Tuesday': [
            (0, 60),     # 9:00-10:00
            (90, 390),   # 10:30-15:30
            (420, 480)   # 16:00-17:00
        ]
    }
}

days = ['Monday', 'Tuesday']
found = False
for day in days:
    constraint = day_constraints[day]
    ryan_busy = schedules['Ryan'].get(day, [])
    adam_busy = schedules['Adam'].get(day, [])
    
    ryan_free = compute_free_intervals(ryan_busy, constraint)
    adam_free = compute_free_intervals(adam_busy, constraint)
    
    candidate = None
    for r_int in ryan_free:
        for a_int in adam_free:
            low = max(r_int[0], a_int[0])
            high = min(r_int[1], a_int[1])
            if high - low >= 30:
                if candidate is None or low < candidate[0]:
                    candidate = (low, high)
    
    if candidate is not None:
        start_time_str = min_to_time(candidate[0])
        end_time_str = min_to_time(candidate[1])
        time_range_str = f"{start_time_str}:{end_time_str}"
        print(day)
        print(time_range_str)
        found = True
        break

if not found:
    print("No suitable time found")