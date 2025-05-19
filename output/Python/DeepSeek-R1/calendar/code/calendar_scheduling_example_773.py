def parse_time(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

roy_schedule = {
    'Monday': [
        ('10:00', '11:30'),
        ('12:00', '13:00'),
        ('14:00', '14:30'),
        ('15:00', '17:00'),
    ],
    'Tuesday': [
        ('10:30', '11:30'),
        ('12:00', '14:30'),
        ('15:00', '15:30'),
        ('16:00', '17:00'),
    ],
    'Wednesday': [
        ('9:30', '11:30'),
        ('12:30', '14:00'),
        ('14:30', '15:30'),
        ('16:30', '17:00'),
    ]
}

work_start = parse_time('09:00')
work_end = parse_time('17:00')
meeting_duration = 60

for day in ['Monday', 'Tuesday', 'Wednesday']:
    busy = []
    for slot in roy_schedule[day]:
        s, e = parse_time(slot[0]), parse_time(slot[1])
        busy.append((s, e))
    busy.sort()
    free = []
    current = work_start
    for s, e in busy:
        if current < s:
            free.append((current, s))
        current = max(current, e)
    if current < work_end:
        free.append((current, work_end))
    for start, end in free:
        if end - start >= meeting_duration:
            meeting_end = start + meeting_duration
            print(f"{day} {format_time(start)}:{format_time(meeting_end)}")
            exit()