def find_meeting_time(participants_busy, work_hours, meeting_duration, day):
    # Convert all time strings to minutes since 9:00 (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    start_work, end_work = work_hours
    start_work_min = time_to_minutes(start_work)
    end_work_min = time_to_minutes(end_work)
    
    # Generate busy intervals in minutes for each participant
    busy_intervals = []
    for participant in participants_busy:
        participant_intervals = []
        for interval in participants_busy[participant]:
            start, end = interval.split(' to ')
            start_min = time_to_minutes(start)
            end_min = time_to_minutes(end)
            participant_intervals.append((start_min, end_min))
        busy_intervals.append(participant_intervals)
    
    # Find all free intervals common to all participants
    common_free = []
    current_time = start_work_min
    
    while current_time + meeting_duration <= end_work_min:
        # Check if current_time is free for all participants
        all_free = True
        for intervals in busy_intervals:
            is_free = True
            for start, end in intervals:
                if start <= current_time < end or start < current_time + meeting_duration <= end or (current_time <= start and current_time + meeting_duration >= end):
                    is_free = False
                    break
            if not is_free:
                all_free = False
                break
        
        if all_free:
            common_free.append((current_time, current_time + meeting_duration))
            break  # We want the earliest possible time
        else:
            current_time += 1  # Check next minute
    
    if not common_free:
        return None
    
    # Convert the earliest common free interval back to HH:MM format
    start, end = common_free[0]
    start_time = minutes_to_time(start)
    end_time = minutes_to_time(end)
    
    return f"{day}: {start_time}:{end_time}"

# Input data
participants_busy = {
    "Lisa": ["9:00 to 9:30", "10:30 to 11:00", "14:00 to 16:00"],
    "Anthony": ["9:00 to 9:30", "11:00 to 11:30", "12:30 to 13:30", "14:00 to 15:00", "15:30 to 16:00", "16:30 to 17:00"]
}
work_hours = ("9:00", "17:00")
meeting_duration = 30  # minutes
day = "Monday"

# Find and print the meeting time
result = find_meeting_time(participants_busy, work_hours, meeting_duration, day)
print(result)