from datetime import datetime, timedelta

def find_meeting_time(participants, day_of_week, meeting_duration):
    # Define start and end times
    start_time = datetime.strptime("09:00", "%H:%M")
    end_time = datetime.strptime("17:00", "%H:%M")
    
    # Create a set of all possible 30-minute slots
    all_slots = []
    current_slot_start = start_time
    while current_slot_start + timedelta(minutes=meeting_duration) <= end_time:
        all_slots.append((current_slot_start, current_slot_start + timedelta(minutes=meeting_duration)))
        current_slot_start += timedelta(minutes=30)
    
    # Parse busy times for each participant and convert them to datetime objects
    busy_times = {}
    for name, times in participants.items():
        busy_times[name] = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in times]
    
    # Eliminate busy slots
    free_slots = all_slots.copy()
    for name, times in busy_times.items():
        for busy_start, busy_end in times:
            slots_to_remove = []
            for slot_start, slot_end in free_slots:
                if not (slot_end <= busy_start or slot_start >= busy_end):  # Overlapping condition
                    slots_to_remove.append((slot_start, slot_end))
            for slot in slots_to_remove:
                free_slots.remove(slot)
    
    # Select the first available slot
    if free_slots:
        meeting_start, meeting_end = free_slots[0]
        return f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}", day_of_week
    else:
        return "No available slot found", day_of_week

# Participants' schedules
participants = {
    'Doris': [('09:00', '11:00'), ('13:30', '14:00'), ('16:00', '16:30')],
    'Theresa': [('10:00', '12:00')],
    'Christian': [],
    'Terry': [('09:30', '10:00'), ('11:30', '12:00'), ('12:30', '13:00'), ('13:30', '14:00'), ('14:30', '15:00'), ('15:30', '17:00')],
    'Carolyn': [('09:00', '10:30'), ('11:00', '11:30'), ('12:00', '13:00'), ('13:30', '14:30'), ('15:00', '17:00')],
    'Kyle': [('09:00', '09:30'), ('11:30', '12:00'), ('12:30', '13:00'), ('14:30', '17:00')]
}

day_of_week = "Monday"
meeting_duration = 30  # in minutes

meeting_time, day = find_meeting_time(participants, day_of_week, meeting_duration)
print(f"Meeting time: {meeting_time} on {day}")