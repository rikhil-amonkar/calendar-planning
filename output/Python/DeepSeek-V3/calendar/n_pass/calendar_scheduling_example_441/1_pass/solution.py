def find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end):
    # Convert all time slots to minutes since midnight for easier comparison
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    
    # Initialize a list to keep track of busy intervals for all participants
    busy_intervals = []
    
    for person, schedules in participants_schedules.items():
        for slot in schedules:
            start, end = map(time_to_minutes, slot.split(' to '))
            busy_intervals.append((start, end))
    
    # Sort all busy intervals by start time
    busy_intervals.sort()
    
    # Merge overlapping or adjacent busy intervals
    merged = []
    for start, end in busy_intervals:
        if not merged:
            merged.append([start, end])
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                merged[-1][1] = max(last_end, end)
            else:
                merged.append([start, end])
    
    # Find the earliest available slot
    previous_end = work_start
    for start, end in merged:
        if start - previous_end >= meeting_duration:
            # Found a slot
            def minutes_to_time(minutes):
                hh = minutes // 60
                mm = minutes % 60
                return f"{hh:02d}:{mm:02d}"
            
            slot_start = minutes_to_time(previous_end)
            slot_end = minutes_to_time(previous_end + meeting_duration)
            return f"{slot_start}:{slot_end}"
        previous_end = max(previous_end, end)
    
    # Check after the last busy interval
    if work_end - previous_end >= meeting_duration:
        def minutes_to_time(minutes):
            hh = minutes // 60
            mm = minutes % 60
            return f"{hh:02d}:{mm:02d}"
        
        slot_start = minutes_to_time(previous_end)
        slot_end = minutes_to_time(previous_end + meeting_duration)
        return f"{slot_start}:{slot_end}"
    
    return None

# Define participants' schedules
participants_schedules = {
    "Joan": ["11:30 to 12:00", "14:30 to 15:00"],
    "Megan": ["9:00 to 10:00", "14:00 to 14:30", "16:00 to 16:30"],
    "Austin": [],
    "Betty": ["9:30 to 10:00", "11:30 to 12:00", "13:30 to 14:00", "16:00 to 16:30"],
    "Judith": ["9:00 to 11:00", "12:00 to 13:00", "14:00 to 15:00"],
    "Terry": ["9:30 to 10:00", "11:30 to 12:30", "13:00 to 14:00", "15:00 to 15:30", "16:00 to 17:00"],
    "Kathryn": ["9:30 to 10:00", "10:30 to 11:00", "11:30 to 13:00", "14:00 to 16:00", "16:30 to 17:00"]
}

# Meeting duration in minutes (30 minutes)
meeting_duration = 30
work_hours_start = "9:00"
work_hours_end = "17:00"

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end)

# Output the result
print(f"Monday {meeting_time}")