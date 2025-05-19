from datetime import datetime, timedelta

# Define the working hours and meeting duration
working_hours_start = datetime.strptime('09:00', '%H:%M')
working_hours_end = datetime.strptime('17:00', '%H:%M')
meeting_duration = timedelta(minutes=30)

# Define the participants' schedules as busy time intervals
schedules = {
    "Steven": [(working_hours_start, working_hours_end)],
    "Roy": [(working_hours_start, working_hours_end)],
    "Cynthia": [
        (datetime.strptime('09:30', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
        (datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
        (datetime.strptime('13:00', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
        (datetime.strptime('15:00', '%H:%M'), datetime.strptime('16:00', '%H:%M')),
    ],
    "Lauren": [
        (datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
        (datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
        (datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
        (datetime.strptime('13:00', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
        (datetime.strptime('14:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
        (datetime.strptime('15:00', '%H:%M'), datetime.strptime('15:30', '%H:%M')),
        (datetime.strptime('16:00', '%H:%M'), working_hours_end),
    ],
    "Robert": [
        (datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
        (datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
        (datetime.strptime('12:30', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
        (datetime.strptime('14:00', '%H:%M'), datetime.strptime('16:00', '%H:%M')),
    ],
}

def find_meeting_time(schedules, duration):
    # Get the free time slots of all participants
    free_time_slots = []
    for participant, busy_slots in schedules.items():
        last_end = working_hours_start
        for busy_start, busy_end in busy_slots:
            if last_end < busy_start:
                free_time_slots.append((last_end, busy_start))
            last_end = max(last_end, busy_end)
        if last_end < working_hours_end:
            free_time_slots.append((last_end, working_hours_end))

    # Check for overlaps in free slots
    available_time_slots = []
    for start, end in free_time_slots:
        if end - start >= duration:
            available_time_slots.append((start, end))

    # Find the earliest available time slot for the meeting
    if available_time_slots:
        earliest_start, earliest_end = available_time_slots[0]
        if earliest_start + duration <= earliest_end:
            meeting_start = earliest_start
            meeting_end = earliest_start + duration
            return meeting_start.strftime('%H:%M'), meeting_end.strftime('%H:%M')
    return None

# Find the meeting time
meeting_time = find_meeting_time(schedules, meeting_duration)
day_of_week = "Monday"
if meeting_time:
    print(f"{meeting_time[0]}:{meeting_time[1]} {day_of_week}")
else:
    print("No available time found.")