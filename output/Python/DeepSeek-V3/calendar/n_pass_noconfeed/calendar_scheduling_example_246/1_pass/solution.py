def find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes):
    # Convert all time slots to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    duration = duration_minutes
    
    # Initialize the free slots for the entire work day
    free_slots = [(work_start, work_end)]
    
    # Process each participant's busy slots to find common free time
    for participant, busy_slots in participants_schedules.items():
        participant_busy = []
        for slot in busy_slots:
            start, end = map(time_to_minutes, slot.split(':'))
            participant_busy.append((start, end))
        
        # Merge overlapping or adjacent busy slots for the participant
        participant_busy.sort()
        merged_busy = []
        for start, end in participant_busy:
            if not merged_busy:
                merged_busy.append((start, end))
            else:
                last_start, last_end = merged_busy[-1]
                if start <= last_end:
                    merged_busy[-1] = (last_start, max(end, last_end))
                else:
                    merged_busy.append((start, end))
        
        # Subtract busy slots from current free slots
        new_free_slots = []
        for free_start, free_end in free_slots:
            current_start = free_start
            for busy_start, busy_end in merged_busy:
                if busy_start >= free_end:
                    break
                if busy_end <= current_start:
                    continue
                if busy_start > current_start:
                    new_free_slots.append((current_start, busy_start))
                current_start = max(current_start, busy_end)
            if current_start < free_end:
                new_free_slots.append((current_start, free_end))
        free_slots = new_free_slots
    
    # Find the first free slot that can accommodate the meeting duration
    for start, end in free_slots:
        if end - start >= duration:
            meeting_start = start
            meeting_end = meeting_start + duration
            # Convert back to HH:MM format
            def minutes_to_time(minutes):
                hh = minutes // 60
                mm = minutes % 60
                return f"{hh:02d}:{mm:02d}"
            return f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    return None

# Define the participants' schedules
participants_schedules = {
    "Jacob": ["13:30:14:00", "14:30:15:00"],
    "Diana": ["09:30:10:00", "11:30:12:00", "13:00:13:30", "16:00:16:30"],
    "Adam": ["09:30:10:30", "11:00:12:30", "15:30:16:00"],
    "Angela": ["09:30:10:00", "10:30:12:00", "13:00:15:30", "16:00:16:30"],
    "Dennis": ["09:00:09:30", "10:30:11:30", "13:00:15:00", "16:30:17:00"]
}

# Meeting parameters
day = "Monday"
work_hours_start = "09:00"
work_hours_end = "17:00"
duration_minutes = 30

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes)

# Output the result
print(f"{day}:{meeting_time}")