from datetime import datetime, timedelta

# Constants
participants = {
    'John': [(datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
             (datetime.strptime('14:00', '%H:%M'), datetime.strptime('14:30', '%H:%M'))],
    'Megan': [(datetime.strptime('12:00', '%H:%M'), datetime.strptime('12:30', '%H:%M')),
              (datetime.strptime('14:00', '%H:%M'), datetime.strptime('15:00', '%H:%M')),
              (datetime.strptime('15:30', '%H:%M'), datetime.strptime('16:00', '%H:%M'))],
    'Brandon': [],
    'Kimberly': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
                 (datetime.strptime('10:00', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
                 (datetime.strptime('11:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
                 (datetime.strptime('15:00', '%H:%M'), datetime.strptime('16:00', '%H:%M')),
                 (datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'Sean': [(datetime.strptime('10:00', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
             (datetime.strptime('11:30', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
             (datetime.strptime('15:00', '%H:%M'), datetime.strptime('15:30', '%H:%M'))],
    'Lori': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
             (datetime.strptime('10:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
             (datetime.strptime('13:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
             (datetime.strptime('16:00', '%H:%M'), datetime.strptime('16:30', '%H:%M'))]
}

# Meeting duration
meeting_duration = timedelta(minutes=30)

# Calculate available time slots
def available_time_slots(participants_schedules, work_start, work_end):
    time_slots = []
    current_time = work_start

    while current_time + meeting_duration <= work_end:
        end_time = current_time + meeting_duration
        if all(not (current_time < end and end_time > start) for schedule in participants_schedules.values() for start, end in schedule):
            time_slots.append((current_time, end_time))
        current_time += timedelta(minutes=1)  # Check each minute for availability
    
    return time_slots

# Work hours on Monday
work_start = datetime.strptime('09:00', '%H:%M')
work_end = datetime.strptime('17:00', '%H:%M')

# Get available time slots
available_slots = available_time_slots(participants, work_start, work_end)

# Choose the first available slot
if available_slots:
    proposed_slot = available_slots[0]
    proposed_time_range = f"{proposed_slot[0].strftime('%H:%M')}:{proposed_slot[1].strftime('%H:%M')}"
    day_of_week = 'Monday'
    print(f"{proposed_time_range} {day_of_week}")
else:
    print("No suitable time found.")