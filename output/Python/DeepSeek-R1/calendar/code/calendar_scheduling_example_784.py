def time_to_min(t):
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def min_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def get_free_slots(busy_intervals, work_start, work_end, filter_start=None):
    busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    prev_end = work_start
    for start, end in busy:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    if filter_start is not None:
        free = [(max(s, filter_start), e) for s, e in free if max(s, filter_start) < e]
    return free

work_hours = (9 * 60, 17 * 60)
days_order = ['Wednesday', 'Tuesday', 'Monday']  # Priority based on Judith's preferences

judith_busy = {
    'Monday': [(time_to_min('12:00'), time_to_min('12:30'))],
    'Wednesday': [(time_to_min('11:30'), time_to_min('12:00'))],
    'Tuesday': []
}

timothy_busy = {
    'Monday': [(time_to_min('09:30'), time_to_min('10:00')),
               (time_to_min('10:30'), time_to_min('11:30')),
               (time_to_min('12:30'), time_to_min('14:00')),
               (time_to_min('15:30'), time_to_min('17:00'))],
    'Tuesday': [(time_to_min('09:30'), time_to_min('13:00')),
                (time_to_min('13:30'), time_to_min('14:00')),
                (time_to_min('14:30'), time_to_min('17:00'))],
    'Wednesday': [(time_to_min('09:00'), time_to_min('09:30')),
                  (time_to_min('10:30'), time_to_min('11:00')),
                  (time_to_min('13:30'), time_to_min('14:30')),
                  (time_to_min('15:00'), time_to_min('15:30')),
                  (time_to_min('16:00'), time_to_min('16:30'))]
}

for day in days_order:
    j_filter = None
    if day == 'Wednesday':
        j_filter = time_to_min('12:00')  # Avoid Wednesday before 12:00
    elif day == 'Monday':
        continue  # Check Monday last
    
    # Get free slots for Judith
    j_busy = judith_busy.get(day, [])
    j_free = get_free_slots(j_busy, work_hours[0], work_hours[1], j_filter)
    
    # Get free slots for Timothy
    t_busy = timothy_busy.get(day, [])
    t_free = get_free_slots(t_busy, work_hours[0], work_hours[1], j_filter)
    
    # Find overlapping slots
    overlap = []
    j_idx = t_idx = 0
    while j_idx < len(j_free) and t_idx < len(t_free):
        j_start, j_end = j_free[j_idx]
        t_start, t_end = t_free[t_idx]
        
        start = max(j_start, t_start)
        end = min(j_end, t_end)
        if start < end:
            overlap.append((start, end))
            if j_end < t_end:
                j_idx += 1
            else:
                t_idx += 1
        else:
            if j_end < t_end:
                j_idx += 1
            else:
                t_idx += 1
    
    # Check for 60-minute slot
    for start, end in overlap:
        if end - start >= 60:
            print(f"{day}:{min_to_time(start)}:{min_to_time(start + 60)}")
            exit()

# Check Monday if no other days found
j_filter = None
j_free = get_free_slots(judith_busy['Monday'], work_hours[0], work_hours[1], j_filter)
t_free = get_free_slots(timothy_busy['Monday'], work_hours[0], work_hours[1], j_filter)

overlap = []
j_idx = t_idx = 0
while j_idx < len(j_free) and t_idx < len(t_free):
    j_start, j_end = j_free[j_idx]
    t_start, t_end = t_free[t_idx]
    
    start = max(j_start, t_start)
    end = min(j_end, t_end)
    if start < end:
        overlap.append((start, end))
        if j_end < t_end:
            j_idx += 1
        else:
            t_idx += 1
    else:
        if j_end < t_end:
            j_idx += 1
        else:
            t_idx += 1

for start, end in overlap:
    if end - start >= 60:
        print(f"Monday:{min_to_time(start)}:{min_to_time(start + 60)}")
        exit()