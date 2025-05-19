def convert_time(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def inverse_convert(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def find_meeting_time(schedules, duration, work_start, work_end):
    work_start_min = convert_time(work_start)
    work_end_min = convert_time(work_end)
    timeline = []

    for person in schedules.values():
        for start, end in person:
            timeline.append((start, end))

    timeline.sort()
    merged = []
    for start, end in timeline:
        if not merged:
            merged.append([start, end])
        else:
            last_end = merged[-1][1]
            if start <= last_end:
                merged[-1][1] = max(last_end, end)
            else:
                merged.append([start, end])

    prev_end = work_start_min
    for interval in merged:
        start, end = interval
        if start - prev_end >= duration:
            return (prev_end, prev_end + duration)
        prev_end = max(prev_end, end)
    if work_end_min - prev_end >= duration:
        return (prev_end, prev_end + duration)
    return None

participants = {
    'Emily': [('10:00', '10:30'), ('16:00', '16:30')],
    'Mason': [],
    'Maria': [('10:30', '11:00'), ('14:00', '14:30')],
    'Carl': [('9:30', '10:00'), ('10:30', '12:30'), ('13:30', '14:00'), ('14:30', '15:30'), ('16:00', '17:00')],
    'David': [('9:30', '11:00'), ('11:30', '12:00'), ('12:30', '13:30'), ('14:00', '15:00'), ('16:00', '17:00')],
    'Frank': [('9:30', '10:30'), ('11:00', '11:30'), ('12:30', '13:30'), ('14:30', '17:00')]
}

# Convert schedules to minutes
converted_schedules = {}
for person, meetings in participants.items():
    converted = []
    for start, end in meetings:
        converted.append((convert_time(start), convert_time(end)))
    converted_schedules[person] = converted

# Find meeting time
meeting_time = find_meeting_time(
    converted_schedules,
    30,
    '9:00',
    '17:00'
)

if meeting_time:
    start, end = meeting_time
    print(f"Monday:{inverse_convert(start)}:{inverse_convert(end)}")
else:
    print("No suitable time found")