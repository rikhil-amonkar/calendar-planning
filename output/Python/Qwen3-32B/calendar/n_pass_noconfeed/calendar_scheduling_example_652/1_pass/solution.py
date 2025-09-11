def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, start_day, end_day):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free_intervals = []
    prev_end = start_day
    for start, end in sorted_busy:
        if prev_end < start:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < end_day:
        free_intervals.append((prev_end, end_day))
    return free_intervals

def find_common_free_slots(jesse_free, lawrence_free):
    common_slots = []
    for j_start, j_end in jesse_free:
        for l_start, l_end in lawrence_free:
            start = max(j_start, l_start)
            end = min(j_end, l_end)
            if start < end:
                duration = end - start
                if duration >= 30:
                    common_slots.append((start, end))
    return common_slots

# Define busy intervals for each participant and day
jesse_busy = {
    'Monday': [
        (13*60 + 30, 14*60 + 0),  # 13:30-14:00
        (14*60 + 30, 15*60 + 0)   # 14:30-15:00
    ],
    'Tuesday': [
        (9*60 + 0, 9*60 + 30),     # 9:00-9:30
        (13*60 + 0, 13*60 + 30),   # 13:00-13:30
        (14*60 + 0, 15*60 + 0)     # 14:00-15:00
    ]
}

lawrence_busy = {
    'Monday': [
        (9*60 + 0, 17*60 + 0)  # 9:00-17:00
    ],
    'Tuesday': [
        (9*60 + 30, 10*60 + 30),  # 9:30-10:30
        (11*60 + 30, 12*60 + 30), # 11:30-12:30
        (13*60 + 0, 13*60 + 30),  # 13:00-13:30
        (14*60 + 30, 15*60 + 0),  # 14:30-15:00
        (15*60 + 30, 16*60 + 30)  # 15:30-16:30
    ]
}

days = ['Monday', 'Tuesday']

for day in days:
    # Get busy intervals for the day
    jesse_day_busy = jesse_busy.get(day, [])
    lawrence_day_busy = lawrence_busy.get(day, [])
    
    # Determine work hours for each participant on this day
    if day == 'Tuesday':
        jesse_start = 9 * 60
        jesse_end = 17 * 60
        lawrence_start = 9 * 60
        lawrence_end = 16 * 60 + 30  # 16:30
    else:  # Monday
        jesse_start = 9 * 60
        jesse_end = 17 * 60
        lawrence_start = 9 * 60
        lawrence_end = 17 * 60
    
    # Compute free intervals for each
    jesse_free = get_free_intervals(jesse_day_busy, jesse_start, jesse_end)
    lawrence_free = get_free_intervals(lawrence_day_busy, lawrence_start, lawrence_end)
    
    # Find common free slots
    common_slots = find_common_free_slots(jesse_free, lawrence_free)
    
    if common_slots:
        # Find earliest slot
        earliest_start, earliest_end = min(common_slots, key=lambda x: x[0])
        # Convert to time strings
        start_time = minutes_to_time(earliest_start)
        end_time = minutes_to_time(earliest_end)
        print(f"{start_time}:{end_time} {day}")
        break  # Since days are checked in order, first valid day is output