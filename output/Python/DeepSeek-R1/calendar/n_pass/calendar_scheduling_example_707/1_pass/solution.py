def time_str_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(busy_list, start_min, end_min):
    busy_intervals = []
    for s, e in busy_list:
        s_min = time_str_to_minutes(s)
        e_min = time_str_to_minutes(e)
        busy_intervals.append((s_min, e_min))
    
    busy_intervals.sort()
    free = []
    current = start_min
    for s, e in busy_intervals:
        if s > current:
            free.append((current, s))
            current = e
        else:
            if e > current:
                current = e
    if current < end_min:
        free.append((current, end_min))
    return free

def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    common = []
    while i < len(intervals1) and j < len(intervals2):
        low = max(intervals1[i][0], intervals2[j][0])
        high = min(intervals1[i][1], intervals2[j][1])
        if low < high:
            common.append((low, high))
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return common

def main():
    ryan_busy = {
        'Monday': [('09:30', '10:00'), ('11:00', '12:00'), ('13:00', '13:30'), ('15:30', '16:00')],
        'Tuesday': [('11:30', '12:30'), ('15:30', '16:00')],
        'Wednesday': [('12:00', '13:00'), ('15:30', '16:00'), ('16:30', '17:00')]
    }
    adam_busy = {
        'Monday': [('09:00', '10:30'), ('11:00', '13:30'), ('14:00', '16:00'), ('16:30', '17:00')],
        'Tuesday': [('09:00', '10:00'), ('10:30', '15:30'), ('16:00', '17:00')],
        'Wednesday': [('09:00', '09:30'), ('10:00', '11:00'), ('11:30', '14:30'), ('15:00', '15:30'), ('16:00', '16:30')]
    }
    
    days = ['Monday', 'Tuesday']
    work_start = 9 * 60
    work_end = 17 * 60
    duration = 30
    
    for day in days:
        if day == 'Monday':
            constraint_start = 14 * 60 + 30
        else:
            constraint_start = work_start
            
        ryan_free = get_free_intervals(ryan_busy[day], constraint_start, work_end)
        adam_free = get_free_intervals(adam_busy[day], constraint_start, work_end)
        common_free = intersect_intervals(ryan_free, adam_free)
        
        for start, end in common_free:
            if end - start >= duration:
                meeting_end = start + duration
                start_str = minutes_to_time_str(start)
                end_str = minutes_to_time_str(meeting_end)
                print(day)
                print(f"{start_str}:{end_str}")
                return

if __name__ == "__main__":
    main()