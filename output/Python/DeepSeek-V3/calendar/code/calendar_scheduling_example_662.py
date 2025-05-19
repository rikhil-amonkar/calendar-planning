def find_meeting_time(gary_schedule, david_schedule, work_hours_start, work_hours_end, meeting_duration, days):
    for day in days:
        # Initialize available time for the day
        available_start = work_hours_start
        available_end = work_hours_end
        
        # Get blocked times for Gary and David on the current day
        gary_blocked = gary_schedule.get(day, [])
        david_blocked = david_schedule.get(day, [])
        
        # Combine and sort all blocked times
        all_blocked = gary_blocked + david_blocked
        all_blocked.sort()
        
        # Merge overlapping or adjacent blocked times
        merged_blocked = []
        for start, end in all_blocked:
            if not merged_blocked:
                merged_blocked.append((start, end))
            else:
                last_start, last_end = merged_blocked[-1]
                if start <= last_end:
                    # Overlapping or adjacent, merge them
                    new_start = min(last_start, start)
                    new_end = max(last_end, end)
                    merged_blocked[-1] = (new_start, new_end)
                else:
                    merged_blocked.append((start, end))
        
        # Find available slots
        current_time = available_start
        for start, end in merged_blocked:
            if current_time < start:
                # Check if the slot is long enough
                if (start - current_time) >= meeting_duration:
                    return day, (current_time, current_time + meeting_duration)
            current_time = max(current_time, end)
        
        # Check the remaining time after the last blocked slot
        if (available_end - current_time) >= meeting_duration:
            return day, (current_time, current_time + meeting_duration)
    
    return None, None

# Define work hours and meeting duration
work_hours_start = 9.0  # 9:00
work_hours_end = 17.0    # 17:00
meeting_duration = 1.0   # 1 hour

# Define schedules
gary_schedule = {
    'Monday': [(9.5, 10.0), (11.0, 13.0), (14.0, 14.5), (16.5, 17.0)],
    'Tuesday': [(9.0, 9.5), (10.5, 11.0), (14.5, 16.0)]
}

david_schedule = {
    'Monday': [(9.0, 9.5), (10.0, 13.0), (14.5, 16.5)],
    'Tuesday': [(9.0, 9.5), (10.0, 10.5), (11.0, 12.5), (13.0, 14.5), (15.0, 16.0), (16.5, 17.0)]
}

# Days to consider
days = ['Monday', 'Tuesday']

# Find meeting time
day, time_slot = find_meeting_time(gary_schedule, david_schedule, work_hours_start, work_hours_end, meeting_duration, days)

if day and time_slot:
    start_hour = int(time_slot[0])
    start_min = int((time_slot[0] - start_hour) * 60)
    end_hour = int(time_slot[1])
    end_min = int((time_slot[1] - end_hour) * 60)
    print(f"{day}: {start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}")
else:
    print("No suitable time found.")