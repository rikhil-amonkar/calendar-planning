def find_meeting_time(participants_schedules, work_hours_start, work_hours_end, duration_minutes, day):
    # Convert all times to minutes since midnight for easier comparison
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    
    # Initialize the list of busy intervals for all participants
    busy_intervals = []
    for schedule in participants_schedules:
        for busy in schedule:
            start, end = map(time_to_minutes, busy.split(' to '))
            busy_intervals.append((start, end))
    
    # Sort all busy intervals by start time
    busy_intervals.sort()
    
    # Merge overlapping or adjacent busy intervals
    merged = []
    for start, end in busy_intervals:
        if not merged:
            merged.append((start, end))
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                # Overlapping or adjacent, merge them
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged[-1] = (new_start, new_end)
            else:
                merged.append((start, end))
    
    # Find available slots by checking gaps between busy intervals and work hours
    available_slots = []
    prev_end = work_start
    
    for start, end in merged:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if prev_end < work_end:
        available_slots.append((prev_end, work_end))
    
    # Check each available slot for sufficient duration
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= duration_minutes:
            # Convert back to HH:MM format
            def minutes_to_time(minutes):
                hh = minutes // 60
                mm = minutes % 60
                return f"{hh:02d}:{mm:02d}"
            
            meeting_start = minutes_to_time(slot_start)
            meeting_end = minutes_to_time(slot_start + duration_minutes)
            return f"{day}: {meeting_start}:{meeting_end}"
    
    return "No suitable time found."

# Define the participants' schedules
james_schedule = [
    "11:30 to 12:00",
    "14:30 to 15:00"
]

john_schedule = [
    "9:30 to 11:00",
    "11:30 to 12:00",
    "12:30 to 13:30",
    "14:30 to 16:30"
]

participants_schedules = [james_schedule, john_schedule]
work_hours_start = "9:00"
work_hours_end = "17:00"
duration_minutes = 60
day = "Monday"

# Find and print the meeting time
print(find_meeting_time(participants_schedules, work_hours_start, work_hours_end, duration_minutes, day))