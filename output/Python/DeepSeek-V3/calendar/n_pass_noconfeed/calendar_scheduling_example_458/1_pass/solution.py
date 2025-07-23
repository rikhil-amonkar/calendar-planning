def find_meeting_time(participants_schedules, duration_minutes=30, work_hours=('09:00', '17:00')):
    from datetime import datetime, timedelta

    # Parse work hours
    work_start = datetime.strptime(work_hours[0], '%H:%M')
    work_end = datetime.strptime(work_hours[1], '%H:%M')

    # Generate all possible 30-minute slots within work hours
    time_slots = []
    current_time = work_start
    while current_time + timedelta(minutes=duration_minutes) <= work_end:
        time_slots.append((current_time, current_time + timedelta(minutes=duration_minutes)))
        current_time += timedelta(minutes=1)  # Check every minute for precision

    # Check each slot against all participants' schedules
    for slot_start, slot_end in time_slots:
        slot_ok = True
        for participant, schedules in participants_schedules.items():
            # Check if participant is free during the slot
            for busy_start, busy_end in schedules:
                busy_start_dt = datetime.strptime(busy_start, '%H:%M')
                busy_end_dt = datetime.strptime(busy_end, '%H:%M')
                if not (slot_end <= busy_start_dt or slot_start >= busy_end_dt):
                    slot_ok = False
                    break
            if not slot_ok:
                break
        if slot_ok:
            # Check Wayne's preference to avoid before 14:00
            if slot_start >= datetime.strptime('14:00', '%H:%M'):
                return slot_start.strftime('%H:%M'), slot_end.strftime('%H:%M')

    return None

# Define participants' schedules
participants_schedules = {
    'Wayne': [],
    'Melissa': [('10:00', '11:00'), ('12:30', '14:00'), ('15:00', '15:30')],
    'Catherine': [],
    'Gregory': [('12:30', '13:00'), ('15:30', '16:00')],
    'Victoria': [('09:00', '09:30'), ('10:30', '11:30'), ('13:00', '14:00'), ('14:30', '15:00'), ('15:30', '16:30')],
    'Thomas': [('10:00', '12:00'), ('12:30', '13:00'), ('14:30', '16:00')],
    'Jennifer': [('09:00', '09:30'), ('10:00', '10:30'), ('11:00', '13:00'), ('13:30', '14:30'), ('15:00', '15:30'), ('16:00', '16:30')]
}

# Find meeting time
meeting_time = find_meeting_time(participants_schedules)
if meeting_time:
    print(f"Monday:{meeting_time[0]}:{meeting_time[1]}")
else:
    print("No suitable time found.")