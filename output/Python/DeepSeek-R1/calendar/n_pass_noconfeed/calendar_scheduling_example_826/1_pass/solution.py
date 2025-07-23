def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time_tuple(minutes):
    h = minutes // 60
    m = minutes % 60
    return h, m

james_busy = {
    'Monday': [('9:00', '9:30'), ('10:30', '11:00'), ('12:30', '13:00'), ('14:30', '15:30'), ('16:30', '17:00')],
    'Tuesday': [('9:00', '11:00'), ('11:30', '12:00'), ('12:30', '15:30'), ('16:00', '17:00')],
    'Wednesday': [('10:00', '11:00'), ('12:00', '13:00'), ('13:30', '16:00')],
    'Thursday': [('9:30', '11:30'), ('12:00', '12:30'), ('13:00', '13:30'), ('14:00', '14:30'), ('16:30', '17:00')]
}

days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
work_start_min = time_to_minutes('9:00')
work_end_min = time_to_minutes('17:00')

for day in days:
    free_intervals = [(work_start_min, work_end_min)]
    if day in james_busy:
        for busy in james_busy[day]:
            b_start = time_to_minutes(busy[0])
            b_end = time_to_minutes(busy[1])
            new_free = []
            for interval in free_intervals:
                if interval[1] <= b_start or interval[0] >= b_end:
                    new_free.append(interval)
                else:
                    if interval[0] < b_start:
                        new_free.append((interval[0], b_start))
                    if interval[1] > b_end:
                        new_free.append((b_end, interval[1]))
            free_intervals = new_free

    for interval in free_intervals:
        start_free, end_free = interval
        if end_free - start_free >= 30:
            slot_start = start_free
            slot_end = slot_start + 30
            start_h, start_m = minutes_to_time_tuple(slot_start)
            end_h, end_m = minutes_to_time_tuple(slot_end)
            time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
            print(f"{day} {time_str}")
            exit(0)

print("No suitable time found")