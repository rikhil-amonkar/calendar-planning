from datetime import datetime, timedelta

# Define participant schedules and preferences
schedules = {
    'Raymond': [
        (datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
        (datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
        (datetime.strptime('13:00', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
        (datetime.strptime('15:00', '%H:%M'), datetime.strptime('15:30', '%H:%M')),
    ],
    'Billy': [
        (datetime.strptime('10:00', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
        (datetime.strptime('12:00', '%H:%M'), datetime.strptime('13:00', '%H:%M')),
        (datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M')),
    ],
    'Donald': [
        (datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
        (datetime.strptime('10:00', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
        (datetime.strptime('12:00', '%H:%M'), datetime.strptime('13:00', '%H:%M')),
        (datetime.strptime('14:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
        (datetime.strptime('16:00', '%H:%M'), datetime.strptime('17:00', '%H:%M')),
    ]
}

# Meeting duration
meeting_duration = timedelta(minutes=30)
work_start = datetime.strptime('09:00', '%H:%M')
work_end = datetime.strptime('17:00', '%H:%M')

# Calculate free time slots
def get_free_slots(schedules, work_start, work_end):
    busy_times = []
    for participant in schedules.values():
        busy_times.extend(participant)
    
    busy_times.sort(key=lambda x: x[0])  # Sort by start time
    
    free_slots = []
    current_start = work_start
    
    for start, end in busy_times:
        if current_start < start:
            free_slots.append((current_start, start))
        current_start = max(current_start, end)

    if current_start < work_end:
        free_slots.append((current_start, work_end))
    
    return free_slots

free_slots = get_free_slots(schedules, work_start, work_end)

# Find the first suitable time slot for the meeting
for start, end in free_slots:
    if end - start >= meeting_duration:
        proposed_start = start
        proposed_end = start + meeting_duration
        if proposed_end <= end:
            day_of_week = proposed_start.strftime('%A')
            print(f"{proposed_start.strftime('%H:%M')}:{proposed_end.strftime('%H:%M')}: {day_of_week}")
            break