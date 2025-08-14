def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: time_to_minutes(x[0]))
    free = []
    previous_end = time_to_minutes(work_start)
    work_end_minutes = time_to_minutes(work_end)
    
    for start, end in sorted_busy:
        start_min = time_to_minutes(start)
        end_min = time_to_minutes(end)
        if previous_end < start_min:
            free.append((previous_end, start_min))
        previous_end = max(previous_end, end_min)
    if previous_end < work_end_minutes:
        free.append((previous_end, work_end_minutes))
    return free

def find_meeting_slot():
    busy_times = {
        'Monday': [('10:30', '11:00'), ('12:00', '12:30'), ('13:00', '15:00'), ('15:30', '16:30')],
        'Tuesday': [('09:00', '12:00'), ('14:00', '15:30'), ('16:30', '17:00')],
        'Wednesday': [('10:30', '11:00'), ('11:30', '12:00'), ('12:30', '13:00'), ('14:00', '14:30'), ('15:00', '16:00')],
    }
    days_order = ['Monday', 'Tuesday']
    work_start = '09:00'
    work_end = '17:00'
    meeting_duration = 30  # in minutes
    
    for day in days_order:
        busy_intervals = busy_times[day]
        free_intervals = get_free_intervals(busy_intervals, work_start, work_end)
        for start_min, end_min in free_intervals:
            duration = end_min - start_min
            if duration >= meeting_duration:
                start_time = minutes_to_time(start_min)
                end_time = minutes_to_time(start_min + meeting_duration)
                return f"{start_time}:{end_time}", day
    return None, None

result, day = find_meeting_slot()
print(f"{day} {result}")