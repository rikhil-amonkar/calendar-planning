def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    min = m % 60
    return f"{h:02d}:{min:02d}"

def get_free_intervals(busy_intervals, work_start=540, work_end=1020):
    busy = sorted([(time_to_minutes(s), time_to_minutes(e)) for s, e in busy_intervals], key=lambda x: x[0])
    free = []
    prev_end = work_start
    for start, end in busy:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

ryan_schedule = {
    'Monday': [('9:30', '10:00'), ('11:00', '12:00'), ('13:00', '13:30'), ('15:30', '16:00')],
    'Tuesday': [('11:30', '12:30'), ('15:30', '16:00')],
    'Wednesday': [('12:00', '13:00'), ('15:30', '16:00'), ('16:30', '17:00')],
}

adam_schedule = {
    'Monday': [('9:00', '10:30'), ('11:00', '13:30'), ('14:00', '16:00'), ('16:30', '17:00')],
    'Tuesday': [('9:00', '10:00'), ('10:30', '15:30'), ('16:00', '17:00')],
    'Wednesday': [('9:00', '9:30'), ('10:00', '11:00'), ('11:30', '14:30'), ('15:00', '15:30'), ('16:00', '16:30')],
}

candidates = []

for day in ['Monday', 'Tuesday']:
    ryan_buses = ryan_schedule.get(day, [])
    adam_buses = adam_schedule.get(day, [])
    ryan_free = get_free_intervals(ryan_buses)
    adam_free = get_free_intervals(adam_buses)
    
    for r_start, r_end in ryan_free:
        for a_start, a_end in adam_free:
            start = max(r_start, a_start)
            end = min(r_end, a_end)
            if start < end and (end - start) >= 30:
                candidates.append((day, start, end))

def get_priority(candidate):
    day, start, end = candidate
    if day == 'Tuesday':
        return 0
    else:
        if start >= 870:
            return 1
        else:
            return 2

sorted_candidates = sorted(candidates, key=lambda x: (get_priority(x), x[1]))

best_candidate = sorted_candidates[0]
day = best_candidate[0]
start = best_candidate[1]
end = best_candidate[2]

start_time = minutes_to_time(start)
end_time = minutes_to_time(end)

print(f"{start_time}:{end_time} {day}")