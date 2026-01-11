from datetime import datetime, timedelta

def generate_free_slots(busy_times, start_time, end_time, duration):
    current = start_time
    free_slots = []
    while current < end_time:
        next_slot_end = current + timedelta(minutes=duration)
        if not any(current < busy_end and next_slot_end > busy_start for busy_start, busy_end in busy_times):
            free_slots.append((current, next_slot_end))
        current += timedelta(minutes=15)  # Check every 15 minutes for precision
    return free_slots

def find_common_slot(jesse_busy, lawrence_busy, start_time, end_time, duration):
    jesse_slots = generate_free_slots(jesse_busy, start_time, end_time, duration)
    lawrence_slots = generate_free_slots(lawrence_busy, start_time, end_time, duration)
    
    for jesse_slot in jesse_slots:
        for lawrence_slot in lawrence_slots:
            if jesse_slot[0] < lawrence_slot[1] and jesse_slot[1] > lawrence_slot[0]:
                # Overlapping slot
                common_start = max(jesse_slot[0], lawrence_slot[0])
                common_end = min(jesse_slot[1], lawrence_slot[1])
                if (common_end - common_start).seconds >= duration * 60:
                    return common_start, common_end
    return None

# Define the work hours and busy times
work_hours = {'Monday': (datetime.strptime('09:00', '%H:%M'), datetime.strptime('17:00', '%H:%M')),
              'Tuesday': (datetime.strptime('09:00', '%H:%M'), datetime.strptime('17:00', '%H:%M'))}

jesse_busy = {
    'Monday': [(datetime.strptime('13:30', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
               (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:00', '%H:%M'))],
    'Tuesday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
                (datetime.strptime('13:00', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
                (datetime.strptime('14:00', '%H:%M'), datetime.strptime('15:00', '%H:%M'))]
}

lawrence_busy = {
    'Monday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'Tuesday': [(datetime.strptime('09:30', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
                (datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:30', '%H:%M')),
                (datetime.strptime('13:00', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
                (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:00', '%H:%M')),
                (datetime.strptime('15:30', '%H:%M'), datetime.strptime('16:30', '%H:%M'))]
}

meeting_duration = 30  # in minutes

# Check for a valid slot on Monday
monday_slot = find_common_slot(jesse_busy['Monday'], lawrence_busy['Monday'], *work_hours['Monday'], meeting_duration)
if monday_slot:
    print(f"Monday, {monday_slot[0].strftime('%H:%M')}:{monday_slot[1].strftime('%H:%M')}")
else:
    # Check for a valid slot on Tuesday
    tuesday_slot = find_common_slot(jesse_busy['Tuesday'], lawrence_busy['Tuesday'], *work_hours['Tuesday'], meeting_duration)
    if tuesday_slot:
        print(f"Tuesday, {tuesday_slot[0].strftime('%H:%M')}:{tuesday_slot[1].strftime('%H:%M')}")
    else:
        print("No available slot found.")