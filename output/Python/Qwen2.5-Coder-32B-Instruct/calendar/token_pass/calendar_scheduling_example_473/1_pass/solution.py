from datetime import datetime, timedelta

def parse_schedule(schedule_str):
    """Parses a string of time blocks and returns a set of occupied 30-minute slots."""
    occupied_slots = set()
    blocks = schedule_str.split(';')
    for block in blocks:
        start, end = block.strip().split(' to ')
        start_time = datetime.strptime(start, '%H:%M')
        end_time = datetime.strptime(end, '%H:%M')
        
        current_time = start_time
        while current_time < end_time:
            occupied_slots.add(current_time.strftime('%H:%M'))
            current_time += timedelta(minutes=30)
    
    return occupied_slots

def find_available_slot(schedules, meeting_duration, work_start='09:00', work_end='17:00'):
    """Finds an available slot for the meeting based on the given schedules."""
    work_start_time = datetime.strptime(work_start, '%H:%M')
    work_end_time = datetime.strptime(work_end, '%H:%M')
    
    # Generate all possible 30-minute slots during work hours
    possible_slots = []
    current_time = work_start_time
    while current_time + timedelta(minutes=meeting_duration) <= work_end_time:
        possible_slots.append(current_time.strftime('%H:%M'))
        current_time += timedelta(minutes=30)
    
    # Parse all schedules to get occupied slots
    occupied_slots = set()
    for schedule in schedules.values():
        occupied_slots.update(parse_schedule(schedule))
    
    # Find the first available slot
    for slot in possible_slots:
        slot_time = datetime.strptime(slot, '%H:%M')
        slot_end_time = slot_time + timedelta(minutes=meeting_duration)
        slot_end_str = slot_end_time.strftime('%H:%M')
        
        # Check if the slot is available for all participants
        if all(slot not in occupied_slots and slot_end_str not in occupied_slots for occupied_slots in schedules.values()):
            return f"{slot}:{slot_end_str}", "Monday"
    
    return None, None

# Define the schedules for each participant
schedules = {
    'Gregory': '9:00 to 9:30; 11:30 to 12:00',
    'Jonathan': '9:00 to 9:30; 12:00 to 12:30; 13:00 to 13:30; 15:00 to 16:00; 16:30 to 17:00',
    'Barbara': '10:00 to 10:30; 13:30 to 14:00',
    'Jesse': '10:00 to 11:00; 12:30 to 14:30',
    'Alan': '9:30 to 11:00; 11:30 to 12:30; 13:00 to 15:30; 16:00 to 17:00',
    'Nicole': '9:00 to 10:30; 11:30 to 12:00; 12:30 to 13:30; 14:00 to 17:00',
    'Catherine': '9:00 to 10:30; 12:00 to 13:30; 15:00 to 15:30; 16:00 to 16:30'
}

# Meeting duration is 30 minutes
meeting_duration = 30

# Find the available slot
time_range, day_of_week = find_available_slot(schedules, meeting_duration)

print(f"Meeting can be scheduled from {time_range} on {day_of_week}.")