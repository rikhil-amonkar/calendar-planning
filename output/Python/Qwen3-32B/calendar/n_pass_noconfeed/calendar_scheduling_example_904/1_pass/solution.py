from datetime import datetime

def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def generate_free_intervals(busy_intervals, work_start=540, work_end=1020):
    # Convert busy times to minutes and sort
    sorted_busy = sorted([(time_to_minutes(s), time_to_minutes(e)) for s, e in busy_intervals])
    free_intervals = []
    prev_end = work_start
    for start, end in sorted_busy:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))
    return free_intervals

def find_overlapping_intervals(intervals1, intervals2):
    i = 0
    j = 0
    overlaps = []
    while i < len(intervals1) and j < len(intervals2):
        s1, e1 = intervals1[i]
        s2, e2 = intervals2[j]
        # Find overlap
        start = max(s1, s2)
        end = min(e1, e2)
        if start < end:
            overlaps.append((start, end))
        # Move the pointer with the earlier end
        if e1 < e2:
            i += 1
        else:
            j += 1
    return overlaps

# Busy times for Daniel and Bradley on each day
daniel_busy = {
    'Monday': [
        ('9:30', '10:30'),
        ('12:00', '12:30'),
        ('13:00', '14:00'),
        ('14:30', '15:00'),
        ('15:30', '16:00'),
    ],
    'Tuesday': [
        ('11:00', '12:00'),
        ('13:00', '13:30'),
        ('15:30', '16:00'),
        ('16:30', '17:00'),
    ],
    'Wednesday': [
        ('9:00', '10:00'),
        ('14:00', '14:30'),
    ],
    'Thursday': [
        ('10:30', '11:00'),
        ('12:00', '13:00'),
        ('14:30', '15:00'),
        ('15:30', '16:00'),
    ],
    'Friday': [
        ('9:00', '9:30'),
        ('11:30', '12:00'),
        ('13:00', '13:30'),
        ('16:30', '17:00'),
    ],
}

bradley_busy = {
    'Monday': [
        ('9:30', '11:00'),
        ('11:30', '12:00'),
        ('12:30', '13:00'),
        ('14:00', '15:00'),
    ],
    'Tuesday': [
        ('10:30', '11:00'),
        ('12:00', '13:00'),
        ('13:30', '14:00'),
        ('15:30', '16:30'),
    ],
    'Wednesday': [
        ('9:00', '10:00'),
        ('11:00', '13:00'),
        ('13:30', '14:00'),
        ('14:30', '17:00'),
    ],
    'Thursday': [
        ('9:00', '12:30'),
        ('13:30', '14:00'),
        ('14:30', '15:00'),
        ('15:30', '16:30'),
    ],
    'Friday': [
        ('9:00', '9:30'),
        ('10:00', '12:30'),
        ('13:00', '13:30'),
        ('14:00', '14:30'),
        ('15:30', '16:30'),
    ],
}

allowed_days = []

# Check for each day if it is allowed by both Daniel and Bradley
for day in ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']:
    # Daniel's constraints
    daniel_allowed = day not in ['Wednesday', 'Thursday']
    # Bradley's constraints
    if day == 'Monday':
        bradley_allowed = False
    elif day == 'Tuesday':
        # Allowed after 12:00, but the day is allowed
        bradley_allowed = True
    elif day == 'Friday':
        bradley_allowed = False
    else:  # Wednesday or Thursday
        bradley_allowed = True
    # Check if both allow
    if daniel_allowed and bradley_allowed:
        allowed_days.append(day)

# Now process each allowed day
for day in allowed_days:
    # Get busy intervals for the day
    daniel_day_busy = daniel_busy.get(day, [])
    bradley_day_busy = bradley_busy.get(day, [])
    
    # Generate free intervals for Daniel
    daniel_free = generate_free_intervals(daniel_day_busy)
    
    # Generate free intervals for Bradley
    bradley_free = generate_free_intervals(bradley_day_busy)
    
    # Apply Bradley's constraints for the day
    if day == 'Tuesday':
        # Filter Bradley's free intervals to start at or after 12:00 (720)
        filtered_bradley = []
        for s, e in bradley_free:
            if s >= 720:
                filtered_bradley.append((s, e))
        bradley_free = filtered_bradley
    
    # Find overlapping intervals
    overlapping = find_overlapping_intervals(daniel_free, bradley_free)
    
    # Check each overlapping interval for a 30-minute slot
    for s, e in overlapping:
        duration = e - s
        if duration >= 30:
            # Find the earliest possible 30-minute slot
            start_time = s
            end_time = start_time + 30
            # Convert to time strings
            start_str = minutes_to_time(start_time)
            end_str = minutes_to_time(end_time)
            print(f"{day}: {start_str}:{end_str}")
            exit()