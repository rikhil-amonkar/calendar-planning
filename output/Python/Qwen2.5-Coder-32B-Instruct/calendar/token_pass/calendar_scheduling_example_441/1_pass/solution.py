def convert_to_minutes(time_str):
    """Converts time in HH:MM format to minutes since the start of the day."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def convert_from_minutes(minutes):
    """Converts minutes since the start of the day to HH:MM format."""
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02}:{minutes:02}"

def find_free_slots(busy_times, start_time, end_time):
    """Finds all free slots in a day given busy times."""
    busy_times.sort()
    current_start = convert_to_minutes(start_time)
    free_slots = []
    
    for start, end in busy_times:
        start_minutes = convert_to_minutes(start)
        end_minutes = convert_to_minutes(end)
        
        if start_minutes > current_start:
            free_slots.append((current_start, start_minutes))
        
        current_start = max(current_start, end_minutes)
    
    if current_start < convert_to_minutes(end_time):
        free_slots.append((current_start, convert_to_minutes(end_time)))
    
    return free_slots

def find_common_slot(free_slots_list, meeting_duration):
    """Finds a common free slot across all participants that fits the meeting duration."""
    # Initialize with the first person's free slots
    common_slots = free_slots_list[0]
    
    for person_slots in free_slots_list[1:]:
        new_common_slots = []
        for start1, end1 in common_slots:
            for start2, end2 in person_slots:
                overlap_start = max(start1, start2)
                overlap_end = min(end1, end2)
                if overlap_end - overlap_start >= meeting_duration:
                    new_common_slots.append((overlap_start, overlap_end))
        common_slots = new_common_slots
    
    if common_slots:
        return common_slots[0]  # Return the first available common slot
    return None

# Define the participants' busy times
busy_times = {
    'Joan': [('11:30', '12:00'), ('14:30', '15:00')],
    'Megan': [('9:00', '10:00'), ('14:00', '14:30'), ('16:00', '16:30')],
    'Austin': [],
    'Betty': [('9:30', '10:00'), ('11:30', '12:00'), ('13:30', '14:00'), ('16:00', '16:30')],
    'Judith': [('9:00', '11:00'), ('12:00', '13:00'), ('14:00', '15:00')],
    'Terry': [('9:30', '10:00'), ('11:30', '12:30'), ('13:00', '14:00'), ('15:00', '15:30'), ('16:00', '17:00')],
    'Kathryn': [('9:30', '10:00'), ('10:30', '11:00'), ('11:30', '13:00'), ('14:00', '16:00'), ('16:30', '17:00')]
}

# Define the work hours and meeting duration
work_start = '9:00'
work_end = '17:00'
meeting_duration = 30  # in minutes

# Find free slots for each participant
free_slots_list = [find_free_slots(busy_times[name], work_start, work_end) for name in busy_times]

# Find a common free slot
common_slot = find_common_slot(free_slots_list, meeting_duration)

if common_slot:
    start_time = convert_from_minutes(common_slot[0])
    end_time = convert_from_minutes(common_slot[1])
    print(f"Meeting time: {start_time}:{end_time} on Monday")
else:
    print("No common time slot found.")