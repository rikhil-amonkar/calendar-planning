def find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end):
    # Convert all time slots to minutes since start of the day for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)

    # Initialize the free slots as the entire work day
    free_slots = [(work_start, work_end)]

    # Process each participant's schedule to find common free times
    for schedule in participants_schedules:
        busy_slots = []
        for busy in schedule:
            start, end = map(time_to_minutes, busy.split(':'))
            busy_slots.append((start, end))
        
        # Sort the busy slots by start time
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
                    new_start = last_start
                    new_end = max(last_end, end)
                    merged_busy[-1] = (new_start, new_end)
                else:
                    merged_busy.append((start, end))
        
        # Calculate free slots for this participant by subtracting busy slots from work hours
        participant_free = []
        prev_end = work_start
        for start, end in merged_busy:
            if start > prev_end:
                participant_free.append((prev_end, start))
            prev_end = max(prev_end, end)
        if prev_end < work_end:
            participant_free.append((prev_end, work_end))
        
        # Intersect participant's free slots with current common free slots
        new_free_slots = []
        i = j = 0
        while i < len(free_slots) and j < len(participant_free):
            slot_start, slot_end = free_slots[i]
            part_start, part_end = participant_free[j]

            # Find the overlapping interval
            overlap_start = max(slot_start, part_start)
            overlap_end = min(slot_end, part_end)

            if overlap_start < overlap_end:
                new_free_slots.append((overlap_start, overlap_end))
            
            # Move the pointer which ends first
            if slot_end < part_end:
                i += 1
            else:
                j += 1
        
        free_slots = new_free_slots
        if not free_slots:
            return None  # No common free time
    
    # Find the first free slot that can accommodate the meeting duration
    meeting_duration_min = time_to_minutes(meeting_duration) - time_to_minutes("0:00")
    for start, end in free_slots:
        if end - start >= meeting_duration_min:
            meeting_end = start + meeting_duration_min
            return (minutes_to_time(start), minutes_to_time(meeting_end))
    
    return None

# Define the participants' schedules
participants_schedules = [
    [],  # Tyler is free all day
    [],  # Kelly is free all day
    ["11:00:11:30", "14:30:15:00"],  # Stephanie
    [],  # Hannah is free all day
    ["9:00:9:30", "10:00:12:00", "12:30:13:00", "14:00:17:00"],  # Joe
    ["9:00:10:30", "11:30:12:00", "13:00:14:00", "14:30:15:30", "16:00:17:00"],  # Diana
    ["9:00:10:00", "10:30:12:00", "12:30:13:00", "13:30:14:00", "14:30:15:30", "16:00:16:30"],  # Deborah
]

meeting_duration = "0:30"
work_hours_start = "9:00"
work_hours_end = "17:00"

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end)

if meeting_time:
    start_time, end_time = meeting_time
    print(f"{start_time}:{end_time}:Monday")
else:
    print("No suitable time found.")