def find_meeting_time():
    # Participant availability
    russell_schedule = {
        'Monday': [(9, 10, 30), (11, 0, 12, 0), (14, 30, 17, 0)],
        'Tuesday': [(9, 13, 30), (14, 0, 17, 0)]
    }
    
    alexander_schedule = {
        'Monday': [(9, 11, 30), (12, 0, 14, 30), (15, 0, 17, 0)],
        'Tuesday': [(9, 10, 0), (13, 14, 0), (15, 15, 30), (16, 16, 30)]
    }
    
    # Meeting duration
    meeting_duration = 1  # in hours
    
    # Function to find free time slots for each day
    def get_free_slots(schedule):
        free_slots = []
        for day, busy_times in schedule.items():
            busy_times.sort()  # Sort busy times
            last_end = 9  # Work starts at 9:00
            for start, end in busy_times:
                if last_end < start:
                    free_slots.append((day, last_end, start))  # Free time found
                last_end = max(last_end, end)  # Update last end time
            if last_end < 17:  # Work ends at 17:00
                free_slots.append((day, last_end, 17))
        return free_slots
    
    # Get free slots for both participants
    russell_free_slots = get_free_slots(russell_schedule)
    alexander_free_slots = get_free_slots(alexander_schedule)
    
    # Check for overlapping free slots that meet the conditions
    for day in russell_schedule.keys():
        russell_slots = [(day, start, end) for d, start, end in russell_free_slots if d == day]
        alexander_slots = [(day, start, end) for d, start, end in alexander_free_slots if d == day]
        
        for r_start, r_end in russell_slots:
            for a_start, a_end in alexander_slots:
                # Check if there's a common slot at least 1 hour long
                start_time = max(r_start, a_start)
                end_time = min(r_end, a_end)
                if end_time - start_time >= meeting_duration:
                    # Check that it's within Russell's preferred times
                    if not (day == 'Tuesday' and start_time < 13.5):
                        # Return in the requested format
                        start_hour = int(start_time)
                        start_minute = int((start_time % 1) * 60)
                        end_hour = int(end_time)
                        end_minute = int((end_time % 1) * 60)
                        return f"{day} {start_hour:02}:{start_minute:02}:{end_hour:02}:{end_minute:02}"

# Output the proposed meeting time
print(find_meeting_time())