def find_meeting_time(arthur_schedule, michael_schedule, meeting_duration, work_start, work_end, excluded_day):
    # Days of the week we are considering
    days = ["Monday", "Tuesday", "Wednesday"]
    
    # Initialize the earliest slot as None
    earliest_slot = None
    
    # Iterate over each day
    for day in days:
        if day == excluded_day:
            continue
        
        # Get the busy slots for Arthur and Michael for the current day
        arthur_busy = arthur_schedule.get(day, [])
        michael_busy = michael_schedule.get(day, [])
        
        # Convert busy slots into a set of minutes since start of the day for easier comparison
        arthur_busy_minutes = set()
        michael_busy_minutes = set()
        
        for start, end in arthur_busy:
            arthur_busy_minutes.update(range(start * 60, end * 60))
        
        for start, end in michael_busy:
            michael_busy_minutes.update(range(start * 60, end * 60))
        
        # Find common free slots
        for start_minute in range(work_start * 60, work_end * 60 - meeting_duration + 1):
            end_minute = start_minute + meeting_duration
            
            # Check if this slot is free for both
            if all(minute not in arthur_busy_minutes for minute in range(start_minute, end_minute)) and \
               all(minute not in michael_busy_minutes for minute in range(start_minute, end_minute)):
                
                # Convert back to hours and minutes
                start_hour, start_min = divmod(start_minute, 60)
                end_hour, end_min = divmod(end_minute, 60)
                
                # Format the time range
                time_range = f"{start_hour:02}:{start_min:02}:{end_hour:02}:{end_min:02}"
                
                # If this is the first valid slot we've found, or earlier than the current earliest, update it
                if earliest_slot is None or (start_hour < earliest_slot[0] or (start_hour == earliest_slot[0] and start_min < earliest_slot[1])):
                    earliest_slot = (start_hour, start_min, end_hour, end_min, day, time_range)
    
    # Output the result
    if earliest_slot:
        _, _, _, _, day, time_range = earliest_slot
        print(f"{time_range} {day}")
    else:
        print("No available time slot found.")

# Define the schedules
arthur_schedule = {
    "Monday": [(11, 11.5), (13.5, 14), (15, 15.5)],
    "Tuesday": [(13, 13.5), (16, 16.5)],
    "Wednesday": [(10, 10.5), (11, 11.5), (12, 12.5), (14, 14.5), (16, 16.5)]
}

michael_schedule = {
    "Monday": [(9, 12), (12.5, 13), (14, 14.5), (15, 17)],
    "Tuesday": [(9.5, 11.5), (12, 13.5), (14, 15.5)],
    "Wednesday": [(10, 12.5), (13, 13.5)]
}

# Meeting parameters
meeting_duration = 30  # in minutes
work_start = 9  # work starts at 9:00
work_end = 17  # work ends at 17:00
excluded_day = "Tuesday"

# Find and print the meeting time
find_meeting_time(arthur_schedule, michael_schedule, meeting_duration, work_start, work_end, excluded_day)