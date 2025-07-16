def find_meeting_time(nancy_schedule, jose_schedule, days, work_hours_start, work_hours_end, duration_minutes):
    duration = duration_minutes / 60  # Convert minutes to hours for easier handling
    
    for day in days:
        # Initialize available slots for the day within work hours
        available_start = work_hours_start
        available_end = work_hours_end
        
        # Get busy slots for Nancy and Jose on the current day
        nancy_busy = nancy_schedule.get(day, [])
        jose_busy = jose_schedule.get(day, [])
        
        # Combine and sort all busy slots
        all_busy = nancy_busy + jose_busy
        all_busy.sort(key=lambda x: x[0])
        
        # Merge overlapping or adjacent busy slots
        merged_busy = []
        for busy in all_busy:
            if not merged_busy:
                merged_busy.append(busy)
            else:
                last_start, last_end = merged_busy[-1]
                current_start, current_end = busy
                if current_start <= last_end:
                    # Overlapping or adjacent, merge them
                    new_start = min(last_start, current_start)
                    new_end = max(last_end, current_end)
                    merged_busy[-1] = (new_start, new_end)
                else:
                    merged_busy.append(busy)
        
        # Find the earliest available slot
        current_time = available_start
        for busy_start, busy_end in merged_busy:
            if busy_start > current_time:
                # Check if there's enough time before the busy slot starts
                if busy_start - current_time >= duration:
                    return day, (current_time, current_time + duration)
            # Update current_time to the end of the busy slot
            current_time = max(current_time, busy_end)
        
        # Check after the last busy slot
        if available_end - current_time >= duration:
            return day, (current_time, current_time + duration)
    
    return None, None

# Define the schedules
nancy_schedule = {
    'Monday': [(10.0, 10.5), (11.5, 12.5), (13.5, 14.0), (14.5, 15.5), (16.0, 17.0)],
    'Tuesday': [(9.5, 10.5), (11.0, 11.5), (12.0, 12.5), (13.0, 13.5), (15.5, 16.0)],
    'Wednesday': [(10.0, 11.5), (13.5, 16.0)],
}

jose_schedule = {
    'Monday': [(9.0, 17.0)],
    'Tuesday': [(9.0, 17.0)],
    'Wednesday': [(9.0, 9.5), (10.0, 12.5), (13.5, 14.5), (15.0, 17.0)],
}

# Define parameters
days_to_check = ['Monday', 'Tuesday', 'Wednesday']
work_start = 9.0
work_end = 17.0
meeting_duration = 0.5  # 30 minutes

# Find the meeting time
day, (start, end) = find_meeting_time(nancy_schedule, jose_schedule, days_to_check, work_start, work_end, meeting_duration * 60)

# Format the output
def float_to_time(time_float):
    hours = int(time_float)
    minutes = int((time_float - hours) * 60)
    return f"{hours:02d}:{minutes:02d}"

start_time = float_to_time(start)
end_time = float_to_time(end)

print(f"{day}: {start_time}:{end_time}")