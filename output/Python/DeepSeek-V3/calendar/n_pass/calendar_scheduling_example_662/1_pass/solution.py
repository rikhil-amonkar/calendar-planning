def find_meeting_time(gary_schedule, david_schedule, days, work_hours, duration):
    for day in days:
        # Initialize available time slots for the day within work hours
        start_work, end_work = work_hours
        available_slots = [(start_work, end_work)]
        
        # Function to subtract busy slots from available slots
        def subtract_busy_slots(available, busy_slots):
            for busy_start, busy_end in busy_slots:
                new_available = []
                for avail_start, avail_end in available:
                    if busy_end <= avail_start or busy_start >= avail_end:
                        # No overlap, keep the available slot
                        new_available.append((avail_start, avail_end))
                    else:
                        # Overlap, split the available slot
                        if avail_start < busy_start:
                            new_available.append((avail_start, busy_start))
                        if busy_end < avail_end:
                            new_available.append((busy_end, avail_end))
                available = new_available
            return available
        
        # Get busy slots for Gary and David on the current day
        gary_busy = gary_schedule.get(day, [])
        david_busy = david_schedule.get(day, [])
        
        # Subtract busy slots from available slots
        available_slots = subtract_busy_slots(available_slots, gary_busy)
        available_slots = subtract_busy_slots(available_slots, david_busy)
        
        # Find the first available slot that fits the duration
        for slot_start, slot_end in available_slots:
            if (slot_end - slot_start) >= duration:
                return day, (slot_start, slot_start + duration)
    
    return None, None

# Define the schedules
gary_schedule = {
    'Monday': [(9.5, 10.0), (11.0, 13.0), (14.0, 14.5), (16.5, 17.0)],
    'Tuesday': [(9.0, 9.5), (10.5, 11.0), (14.5, 16.0)],
}

david_schedule = {
    'Monday': [(9.0, 9.5), (10.0, 13.0), (14.5, 16.5)],
    'Tuesday': [(9.0, 9.5), (10.0, 10.5), (11.0, 12.5), (13.0, 14.5), (15.0, 16.0), (16.5, 17.0)],
}

# Define the days to check and work hours
days = ['Monday', 'Tuesday']
work_hours = (9.0, 17.0)
duration = 1.0  # 1 hour

# Find the meeting time
day, time_slot = find_meeting_time(gary_schedule, david_schedule, days, work_hours, duration)

if day and time_slot:
    start, end = time_slot
    # Convert float hours to HH:MM format
    def float_to_time(time_float):
        hours = int(time_float)
        minutes = int((time_float - hours) * 60)
        return f"{hours:02d}:{minutes:02d}"
    
    start_time = float_to_time(start)
    end_time = float_to_time(end)
    print(f"{day}: {start_time}:{end_time}")
else:
    print("No suitable time found.")