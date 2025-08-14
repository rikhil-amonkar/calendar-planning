def get_free_intervals(busy_intervals, work_start=540, work_end=1020):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free_intervals = []
    prev_end = work_start
    for start, end in sorted_busy:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))
    return free_intervals

def interval_overlap(a, b):
    start = max(a[0], b[0])
    end = min(a[1], b[1])
    if start < end:
        return (start, end)
    return None

def apply_day_constraints(free_intervals, day_constraints_start):
    adjusted = []
    for s, e in free_intervals:
        if e <= day_constraints_start:
            continue
        new_s = max(s, day_constraints_start)
        if new_s < e:
            adjusted.append((new_s, e))
    return adjusted

# Define busy intervals for each person and day
# Betty's busy intervals
busy_betty_monday = [
    (10*60, 10*60 + 30),  # 10:00-10:30
    (13*60 + 30, 14*60),  # 13:30-14:00
    (15*60, 15*60 + 30),  # 15:00-15:30
    (16*60, 16*60 + 30)   # 16:00-16:30
]
busy_betty_tuesday = [
    (9*60, 9*60 + 30),  # 9:00-9:30
    (11*60 + 30, 12*60),  # 11:30-12:00
    (12*60 + 30, 13*60),  # 12:30-13:00
    (13*60 + 30, 14*60),  # 13:30-14:00
    (16*60 + 30, 17*60)   # 16:30-17:00
]
busy_betty_wednesday = [
    (9*60 + 30, 10*60 + 30),  # 9:30-10:30
    (13*60, 13*60 + 30),  # 13:00-13:30
    (14*60, 14*60 + 30)   # 14:00-14:30
]
busy_betty_thursday = [
    (9*60 + 30, 10*60),  # 9:30-10:00
    (11*60 + 30, 12*60),  # 11:30-12:00
    (14*60, 14*60 + 30),  # 14:00-14:30
    (15*60, 15*60 + 30),  # 15:00-15:30
    (16*60 + 30, 17*60)   # 16:30-17:00
]

# Scott's busy intervals
busy_scott_monday = [
    (9*60 + 30, 15*60),  # 9:30-15:00
    (15*60 + 30, 16*60),  # 15:30-16:00
    (16*60 + 30, 17*60)   # 16:30-17:00
]
busy_scott_tuesday = [
    (9*60, 9*60 + 30),  # 9:00-9:30
    (10*60, 11*60),  # 10:00-11:00
    (11*60 + 30, 12*60),  # 11:30-12:00
    (12*60 + 30, 13*60 + 30),  # 12:30-13:30
    (14*60, 15*60),  # 14:00-15:00
    (16*60, 16*60 + 30)   # 16:00-16:30
]
busy_scott_wednesday = [
    (9*60 + 30, 12*60 + 30),  # 9:30-12:30
    (13*60, 13*60 + 30),  # 13:00-13:30
    (14*60, 14*60 + 30),  # 14:00-14:30
    (15*60, 15*60 + 30),  # 15:00-15:30
    (16*60, 16*60 + 30)   # 16:00-16:30
]
busy_scott_thursday = [
    (9*60, 9*60 + 30),  # 9:00-9:30
    (10*60, 10*60 + 30),  # 10:00-10:30
    (11*60, 12*60),  # 11:00-12:00
    (12*60 + 30, 13*60),  # 12:30-13:00
    (15*60, 16*60),  # 15:00-16:00
    (16*60 + 30, 17*60)   # 16:30-17:00
]

days_order = ['Tuesday', 'Thursday', 'Wednesday']

for day in days_order:
    if day == 'Monday':
        continue
    # Get Betty's busy intervals
    if day == 'Monday':
        betty_busy = busy_betty_monday
    elif day == 'Tuesday':
        betty_busy = busy_betty_tuesday
    elif day == 'Wednesday':
        betty_busy = busy_betty_wednesday
    else:  # Thursday
        betty_busy = busy_betty_thursday
    # Get Scott's busy intervals
    if day == 'Monday':
        scott_busy = busy_scott_monday
    elif day == 'Tuesday':
        scott_busy = busy_scott_tuesday
    elif day == 'Wednesday':
        scott_busy = busy_scott_wednesday
    else:  # Thursday
        scott_busy = busy_scott_thursday
    # Compute free intervals for Betty
    betty_free = get_free_intervals(betty_busy)
    # Apply day constraints
    if day in ['Tuesday', 'Thursday']:
        betty_free = apply_day_constraints(betty_free, 900)  # 15:00
    else:
        betty_free = apply_day_constraints(betty_free, 0)  # no constraint
    # Compute free intervals for Scott
    scott_free = get_free_intervals(scott_busy)
    # Find overlapping intervals
    overlapping = []
    for b in betty_free:
        for s in scott_free:
            overlap = interval_overlap(b, s)
            if overlap:
                overlapping.append(overlap)
    # Check for intervals >=30 minutes
    for interval in sorted(overlapping, key=lambda x: x[0]):
        start, end = interval
        if end - start >= 30:
            # Convert to time strings
            start_time = f"{start//60:02d}:{start%60:02d}"
            end_time = f"{end//60:02d}:{end%60:02d}"
            print(f"{day} {start_time}:{end_time}")
            exit()

# If no solution found in priority days, check other days (though problem says there is one)
# But according to the problem, there is a solution, so this should not be needed