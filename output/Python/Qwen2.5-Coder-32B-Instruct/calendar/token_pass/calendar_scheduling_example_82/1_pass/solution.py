def find_meeting_time(schedules, meeting_duration, work_start, work_end, day_of_week):
    from datetime import datetime, timedelta

    # Convert times to datetime objects for easier manipulation
    work_start = datetime.strptime(work_start, '%H:%M')
    work_end = datetime.strptime(work_end, '%H:%M')
    meeting_duration = timedelta(minutes=meeting_duration)

    # Parse schedules into lists of busy times
    busy_times = []
    for person, schedule in schedules.items():
        busy_times.append([])
        for start_str, end_str in schedule:
            start = datetime.strptime(start_str, '%H:%M')
            end = datetime.strptime(end_str, '%H:%M')
            busy_times[-1].append((start, end))

    # Find free slots for each person
    free_slots = []
    for person_busy_times in busy_times:
        current_time = work_start
        person_free_slots = []
        for start, end in person_busy_times:
            if current_time < start:
                person_free_slots.append((current_time, start))
            current_time = max(current_time, end)
        if current_time < work_end:
            person_free_slots.append((current_time, work_end))
        free_slots.append(person_free_slots)

    # Find common free slots
    common_free_slots = free_slots[0]
    for other_person_free_slots in free_slots[1:]:
        new_common_free_slots = []
        for start1, end1 in common_free_slots:
            for start2, end2 in other_person_free_slots:
                overlap_start = max(start1, start2)
                overlap_end = min(end1, end2)
                if overlap_start < overlap_end:
                    new_common_free_slots.append((overlap_start, overlap_end))
        common_free_slots = new_common_free_slots

    # Find a common free slot that fits the meeting duration
    for start, end in common_free_slots:
        if end - start >= meeting_duration:
            return f"{start.strftime('%H:%M')}:{end.strftime('%H:%M')} {day_of_week}"

    return "No suitable time found"

# Define the schedules
schedules = {
    'Michael': [('09:30', '10:30'), ('15:00', '15:30'), ('16:00', '16:30')],
    'Eric': [],
    'Arthur': [('09:00', '12:00'), ('13:00', '15:00'), ('15:30', '16:00'), ('16:30', '17:00')]
}

# Define the meeting duration and work hours
meeting_duration = 30
work_start = '09:00'
work_end = '17:00'
day_of_week = 'Monday'

# Find and print the meeting time
meeting_time = find_meeting_time(schedules, meeting_duration, work_start, work_end, day_of_week)
print(meeting_time)