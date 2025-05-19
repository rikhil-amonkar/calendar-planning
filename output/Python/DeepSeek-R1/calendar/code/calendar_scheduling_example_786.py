def time_to_minutes(time):
    return time[0] * 60 + time[1]

def minutes_to_time(m):
    return (m // 60, m % 60)

def get_free_intervals(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    prev_end = work_start
    for start, end in sorted_busy:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def find_overlapping_intervals(a, b):
    overlapping = []
    i = j = 0
    while i < len(a) and j < len(b):
        a_start, a_end = a[i]
        b_start, b_end = b[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            overlapping.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return overlapping

work_hours = (9, 0), (17, 0)
work_start = time_to_minutes(work_hours[0])
work_end = time_to_minutes(work_hours[1])

schedule = {
    'Amy': {
        'Wednesday': [( (11, 0), (11, 30) ), ( (13, 30), (14, 0) )]
    },
    'Pamela': {
        'Monday': [( (9, 0), (10, 30) ), ( (11, 0), (16, 30) )],
        'Tuesday': [( (9, 0), (9, 30) ), ( (10, 0), (17, 0) )],
        'Wednesday': [( (9, 0), (9, 30) ), ( (10, 0), (11, 0) ), ( (11, 30), (13, 30) ), ( (14, 30), (15, 0) ), ( (16, 0), (16, 30) )]
    }
}

days_order = ['Wednesday', 'Tuesday', 'Monday']

for day in days_order:
    amy_busy = schedule['Amy'].get(day, [])
    pamela_busy = schedule['Pamela'].get(day, [])
    
    amy_busy_min = [ (time_to_minutes(s), time_to_minutes(e)) for s, e in amy_busy ]
    pamela_busy_min = [ (time_to_minutes(s), time_to_minutes(e)) for s, e in pamela_busy ]
    
    amy_free = get_free_intervals(amy_busy_min, work_start, work_end)
    pamela_free = get_free_intervals(pamela_busy_min, work_start, work_end)
    
    overlapping = find_overlapping_intervals(amy_free, pamela_free)
    
    for interval in overlapping:
        start, end = interval
        duration = end - start
        if duration >= 30:
            preferred = False
            if day in ['Tuesday', 'Wednesday']:
                if start >= time_to_minutes((16, 0)):
                    preferred = True
            elif day == 'Monday':
                preferred = False
            
            if (day != 'Monday' and preferred) or (day == 'Monday' and not preferred):
                start_time = minutes_to_time(start)
                end_time = minutes_to_time(start + 30)
                print(f"{day} {start_time[0]:02}:{start_time[1]:02}:{end_time[0]:02}:{end_time[1]:02}")
                exit()

# Fallback to first available slot if preferences couldn't be met (not needed per problem statement)