from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, work_start, work_end):
    # Convert work hours to datetime objects
    work_start_dt = datetime.strptime(work_start, '%H:%M')
    work_end_dt = datetime.strptime(work_end, '%H:%M')
    
    # Initialize a list to hold free time slots for each participant
    free_slots = []
    
    # Iterate over each participant to determine their free slots
    for participant, busy_times in participants.items():
        current_time = work_start_dt
        participant_free_slots = []
        
        # Add a dummy busy time at the end of work hours to simplify logic
        busy_times.append((work_end, 'dummy'))
        
        for busy_start, busy_end in busy_times:
            busy_start_dt = datetime.strptime(busy_start, '%H:%M')
            
            # If there is a gap between current time and the start of the next busy time
            if current_time < busy_start_dt:
                participant_free_slots.append((current_time.strftime('%H:%M'), busy_start))
            
            # Update current time to the end of the busy period
            current_time = datetime.strptime(busy_end, '%H:%M')
        
        # Store the free slots for the current participant
        free_slots.append(participant_free_slots)
    
    # Find the intersection of all free slots
    common_free_slots = free_slots[0]
    
    for slots in free_slots[1:]:
        new_common_slots = []
        for start1, end1 in common_free_slots:
            for start2, end2 in slots:
                # Find the overlap between two time slots
                overlap_start = max(start1, start2)
                overlap_end = min(end1, end2)
                
                # Check if the overlap is long enough for the meeting
                if datetime.strptime(overlap_end, '%H:%M') - datetime.strptime(overlap_start, '%H:%M') >= timedelta(minutes=meeting_duration):
                    new_common_slots.append((overlap_start, overlap_end))
        
        common_free_slots = new_common_slots
    
    # Output the first valid time slot found
    if common_free_slots:
        return f"{common_free_slots[0][0]}:{common_free_slots[0][1]}:Monday"
    else:
        return "No suitable time found"

# Define participants' schedules
participants = {
    'Juan': [('9:00', '10:30'), ('15:30', '16:00')],
    'Marilyn': [('11:00', '11:30'), ('12:30', '13:00')],
    'Ronald': [('9:00', '10:30'), ('12:00', '12:30'), ('13:00', '13:30'), ('14:00', '16:30')]
}

# Meeting duration in minutes
meeting_duration = 30

# Work hours
work_start = '9:00'
work_end = '17:00'

# Find and print the meeting time
print(find_meeting_time(participants, meeting_duration, work_start, work_end))