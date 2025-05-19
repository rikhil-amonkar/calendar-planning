from datetime import datetime, timedelta

# Define work hours and participants
work_start = datetime.strptime('09:00', '%H:%M')
work_end = datetime.strptime('17:00', '%H:%M')
meeting_duration = timedelta(minutes=30)
participants_schedule = {
    'Emily': [(datetime.strptime('10:00', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
              (datetime.strptime('16:00', '%H:%M'), datetime.strptime('16:30', '%H:%M'))],
    'Mason': [],
    'Maria': [(datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
              (datetime.strptime('14:00', '%H:%M'), datetime.strptime('14:30', '%H:%M'))],
    'Carl': [(datetime.strptime('09:30', '%H:%M'), datetime.strptime('10:00', '%H:%M')),
             (datetime.strptime('10:30', '%H:%M'), datetime.strptime('12:30', '%H:%M')),
             (datetime.strptime('13:30', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
             (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:30', '%H:%M')),
             (datetime.strptime('16:00', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'David': [(datetime.strptime('09:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
              (datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
              (datetime.strptime('12:30', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
              (datetime.strptime('14:00', '%H:%M'), datetime.strptime('15:00', '%H:%M')),
              (datetime.strptime('16:00', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'Frank': [(datetime.strptime('09:30', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
              (datetime.strptime('11:00', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
              (datetime.strptime('12:30', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
              (datetime.strptime('14:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
}

# Find common free slots for all participants
def find_meeting_time(participants_schedule, work_start, work_end, meeting_duration):
    # Create a list of all busy times
    busy_times = []
    for schedule in participants_schedule.values():
        for start, end in schedule:
            busy_times.append((start, end))

    # Create a list of free time slots
    free_times = []
    current_time = work_start

    while current_time + meeting_duration <= work_end:
        # Check if current_time is free for all participants
        is_free = True
        for start, end in busy_times:
            if start <= current_time < end or start < current_time + meeting_duration <= end:
                is_free = False
                break
        
        if is_free:
            free_times.append(current_time)
        
        current_time += timedelta(minutes=1)  # Check next minute
        
    if free_times:
        return free_times[0], free_times[0] + meeting_duration
    return None, None

# Get proposed meeting time
proposed_start, proposed_end = find_meeting_time(participants_schedule, work_start, work_end, meeting_duration)

# Output result
if proposed_start and proposed_end:
    print(f"Proposed meeting time: {proposed_start.strftime('%H:%M')} - {proposed_end.strftime('%H:%M')} on Monday")
else:
    print("No available time found")