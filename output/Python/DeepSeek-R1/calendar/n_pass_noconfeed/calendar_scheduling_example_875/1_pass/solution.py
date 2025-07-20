def time_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def compute_free(busy_list, work_start, work_end):
    if not busy_list:
        return [(work_start, work_end)]
    busy_minutes = []
    for (s, e) in busy_list:
        s_min = time_to_minutes(s)
        e_min = time_to_minutes(e)
        busy_minutes.append((s_min, e_min))
    busy_minutes.sort(key=lambda x: x[0])
    merged = []
    start, end = busy_minutes[0]
    for i in range(1, len(busy_minutes)):
        s, e = busy_minutes[i]
        if s <= end:
            end = max(end, e)
        else:
            merged.append((start, end))
            start, end = s, e
    merged.append((start, end))
    free = []
    current = work_start
    for (s, e) in merged:
        if current < s:
            free.append((current, s))
        current = e
    if current < work_end:
        free.append((current, work_end))
    return free

def main():
    natalie_busy = {
        'Monday': [('9:00', '9:30'), ('10:00', '12:00'), ('12:30', '13:00'), ('14:00', '14:30'), ('15:00', '16:30')],
        'Tuesday': [('9:00', '9:30'), ('10:00', '10:30'), ('12:30', '14:00'), ('16:00', '17:00')],
        'Wednesday': [('11:00', '11:30'), ('16:00', '16:30')],
        'Thursday': [('10:00', '11:00'), ('11:30', '15:00'), ('15:30', '16:00'), ('16:30', '17:00')]
    }
    william_busy = {
        'Monday': [('9:30', '11:00'), ('11:30', '17:00')],
        'Tuesday': [('9:00', '13:00'), ('13:30', '16:00')],
        'Wednesday': [('9:00', '12:30'), ('13:00', '14:30'), ('15:30', '16:00'), ('16:30', '17:00')],
        'Thursday': [('9:00', '10:30'), ('11:00', '11:30'), ('12:00', '12:30'), ('13:00', '14:00'), ('15:00', '17:00')]
    }
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    work_start = time_to_minutes('9:00')
    work_end = time_to_minutes('17:00')
    for day in days:
        free_natalie = compute_free(natalie_busy.get(day, []), work_start, work_end)
        free_william = compute_free(william_busy.get(day, []), work_start, work_end)
        for intv1 in free_natalie:
            for intv2 in free_william:
                low = max(intv1[0], intv2[0])
                high = min(intv1[1], intv2[1])
                if high - low >= 60:
                    meeting_start = low
                    meeting_end = low + 60
                    s_time = minutes_to_time(meeting_start)
                    e_time = minutes_to_time(meeting_end)
                    time_output = f"{s_time}:{e_time}"
                    print(day)
                    print(time_output)
                    return

if __name__ == "__main__":
    main()