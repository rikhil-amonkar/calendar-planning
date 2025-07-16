def find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes):
    # Convert work hours to minutes since midnight for easier calculation
    work_start = work_hours_start * 60
    work_end = work_hours_end * 60
    
    # Initialize a list to keep track of busy intervals for all participants
    all_busy_intervals = []
    
    for schedule in participants_schedules:
        for interval in schedule:
            start_hour, start_minute, end_hour, end_minute = interval
            start = start_hour * 60 + start_minute
            end = end_hour * 60 + end_minute
            all_busy_intervals.append((start, end))
    
    # Sort all busy intervals by start time
    all_busy_intervals.sort()
    
    # Merge overlapping or adjacent intervals
    merged_intervals = []
    for interval in all_busy_intervals:
        if not merged_intervals:
            merged_intervals.append(interval)
        else:
            last_start, last_end = merged_intervals[-1]
            current_start, current_end = interval
            if current_start <= last_end:
                # Overlapping or adjacent intervals, merge them
                new_start = last_start
                new_end = max(last_end, current_end)
                merged_intervals[-1] = (new_start, new_end)
            else:
                merged_intervals.append(interval)
    
    # Find available slots between work hours and busy intervals
    available_slots = []
    previous_end = work_start
    
    for interval in merged_intervals:
        start, end = interval
        if start > previous_end:
            available_slots.append((previous_end, start))
        previous_end = max(previous_end, end)
    
    # Check the slot after the last busy interval
    if previous_end < work_end:
        available_slots.append((previous_end, work_end))
    
    # Find the first available slot that can fit the meeting duration
    duration = duration_minutes
    for slot in available_slots:
        start, end = slot
        if end - start >= duration:
            meeting_start = start
            meeting_end = meeting_start + duration
            # Convert back to hours and minutes
            start_hour = meeting_start // 60
            start_minute = meeting_start % 60
            end_hour = meeting_end // 60
            end_minute = meeting_end % 60
            return (
                f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}",
                day
            )
    
    return None, None

# Define the participants' schedules
participants_schedules = [
    # Doris: 9:00-11:00, 13:30-14:00, 16:00-16:30
    [(9, 0, 11, 0), (13, 30, 14, 0), (16, 0, 16, 30)],
    # Theresa: 10:00-12:00
    [(10, 0, 12, 0)],
    # Christian: no meetings
    [],
    # Terry: 9:30-10:00, 11:30-12:00, 12:30-13:00, 13:30-14:00, 14:30-15:00, 15:30-17:00
    [(9, 30, 10, 0), (11, 30, 12, 0), (12, 30, 13, 0), (13, 30, 14, 0), (14, 30, 15, 0), (15, 30, 17, 0)],
    # Carolyn: 9:00-10:30, 11:00-11:30, 12:00-13:00, 13:30-14:30, 15:00-17:00
    [(9, 0, 10, 30), (11, 0, 11, 30), (12, 0, 13, 0), (13, 30, 14, 30), (15, 0, 17, 0)],
    # Kyle: 9:00-9:30, 11:30-12:00, 12:30-13:00, 14:30-17:00
    [(9, 0, 9, 30), (11, 30, 12, 0), (12, 30, 13, 0), (14, 30, 17, 0)]
]

# Define meeting parameters
day = "Monday"
work_hours_start = 9
work_hours_end = 17
duration_minutes = 30

# Find the meeting time
meeting_time, meeting_day = find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes)

# Output the result
print(f"{{{meeting_time}}} {meeting_day}")