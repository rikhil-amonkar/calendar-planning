from datetime import datetime, timedelta

# Define the working hours
start_of_day = datetime.strptime('09:00', '%H:%M')
end_of_day = datetime.strptime('17:00', '%H:%M')

# Define the busy schedules of each participant in terms of (start, end) tuples
schedules = {
    "Melissa": [(datetime.strptime('10:00', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
                 (datetime.strptime('12:30', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
                 (datetime.strptime('15:00', '%H:%M'), datetime.strptime('15:30', '%H:%M'))],
    "Gregory": [(datetime.strptime('12:30', '%H:%M'), datetime.strptime('13:00', '%H:%M')),
                (datetime.strptime('15:30', '%H:%M'), datetime.strptime('16:00', '%H:%M'))],
    "Victoria": [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
                 (datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
                 (datetime.strptime('13:00', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
                 (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:00', '%H:%M')),
                 (datetime.strptime('15:30', '%H:%M'), datetime.strptime('16:30', '%H:%M'))],
    "Thomas": [(datetime.strptime('10:00', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
               (datetime.strptime('12:30', '%H:%M'), datetime.strptime('13:00', '%H:%M')),
               (datetime.strptime('14:30', '%H:%M'), datetime.strptime('16:00', '%H:%M'))],
    "Jennifer": [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
                 (datetime.strptime('10:00', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
                 (datetime.strptime('11:00', '%H:%M'), datetime.strptime('13:00', '%H:%M')),
                 (datetime.strptime('13:30', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
                 (datetime.strptime('15:00', '%H:%M'), datetime.strptime('15:30', '%H:%M')),
                 (datetime.strptime('16:00', '%H:%M'), datetime.strptime('16:30', '%H:%M'))]
}

# Meeting duration
meeting_duration = timedelta(minutes=30)

# Free time slots within working hours
free_slots = []
current_time = start_of_day

while current_time + meeting_duration <= end_of_day:
    # Define the time slot to check
    slot_end = current_time + meeting_duration
    is_free = True
    
    # Check if anyone is busy during this slot
    for busy_times in schedules.values():
        for start, end in busy_times:
            if start < slot_end and current_time < end:
                is_free = False
                break
        if not is_free:
            break
    
    # Check Wayne's preference
    if is_free and current_time < datetime.strptime('14:00', '%H:%M'):
        is_free = False
        
    if is_free:
        free_slots.append((current_time, slot_end))
    
    current_time += timedelta(minutes=1)

# Select the first available slot
if free_slots:
    proposed_time = free_slots[0]
    print(f"Meeting proposed from {proposed_time[0].strftime('%H:%M')} to {proposed_time[1].strftime('%H:%M')} on Monday")
else:
    print("No available slot found.")

# Output the result in HH:MM:HH:MM format along with the day of the week
if free_slots:
    print(f"{proposed_time[0].strftime('%H:%M')}:{proposed_time[1].strftime('%H:%M')} Monday")