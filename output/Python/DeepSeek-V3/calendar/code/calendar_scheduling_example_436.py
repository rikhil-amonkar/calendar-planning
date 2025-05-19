def find_meeting_time(participants_schedules, work_hours_start, work_hours_end, meeting_duration):
    # Convert time strings to minutes since start of day for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    
    # Initialize the available slots as the entire work day
    available_slots = [(work_start, work_end)]
    
    # Process each participant's schedule to find common free slots
    for schedule in participants_schedules:
        busy_slots = []
        for busy in schedule:
            start, end = map(time_to_minutes, busy.split(':'))
            busy_slots.append((start, end))
        
        # Sort busy slots by start time
        busy_slots.sort()
        
        # Merge overlapping or adjacent busy slots
        merged_busy = []
        for start, end in busy_slots:
            if not merged_busy:
                merged_busy.append((start, end))
            else:
                last_start, last_end = merged_busy[-1]
                if start <= last_end:
                    # Overlapping or adjacent, merge them
                    new_start = min(last_start, start)
                    new_end = max(last_end, end)
                    merged_busy[-1] = (new_start, new_end)
                else:
                    merged_busy.append((start, end))
        
        # Subtract busy slots from available slots
        new_available = []
        for avail_start, avail_end in available_slots:
            current_start = avail_start
            for busy_start, busy_end in merged_busy:
                if busy_start > current_start:
                    # Add the free slot before the busy slot
                    new_available.append((current_start, busy_start))
                current_start = max(current_start, busy_end)
            if current_start < avail_end:
                new_available.append((current_start, avail_end))
        available_slots = new_available
    
    # Find the first available slot that fits the meeting duration
    meeting_duration_min = time_to_minutes(meeting_duration)
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= meeting_duration_min:
            meeting_end = slot_start + meeting_duration_min
            return (minutes_to_time(slot_start), minutes_to_time(meeting_end)
    
    return None

# Define participants' schedules
participants_schedules = [
    ["13:30:14:00", "14:30:15:00"],  # Patrick
    ["09:00:09:30", "11:00:11:30", "12:00:12:30", "14:30:15:00", "16:00:17:00"],  # Shirley
    ["09:00:09:30", "10:30:11:00", "11:30:12:00", "13:00:13:30", "16:00:17:00"],  # Jeffrey
    ["11:30:12:00", "15:00:15:30"],  # Gloria
    ["09:00:09:30", "10:30:12:00", "14:00:17:00"],  # Nathan
    ["09:00:09:30", "10:00:11:00", "12:30:15:00", "15:30:16:30"],  # Angela
    ["09:00:09:30", "10:00:10:30", "11:00:14:00", "14:30:16:30"],  # David
]

# Define work hours and meeting duration
work_hours_start = "09:00"
work_hours_end = "17:00"
meeting_duration = "00:30"

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, work_hours_start, work_hours_end, meeting_duration)

if meeting_time:
    start_time, end_time = meeting_time
    print(f"{start_time}:{end_time}")
    print("Monday")
else:
    print("No suitable time found.")