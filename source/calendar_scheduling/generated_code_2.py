def find_meeting_time(janice_busy, richard_busy, work_hours, duration):
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    start_hour, end_hour = work_hours
    
    for day in days:
        # Get busy slots for the day
        janice_day = [slot for slot in janice_busy if slot[0] == day]
        richard_day = [slot for slot in richard_busy if slot[0] == day]
        
        # Combine and sort all busy slots
        busy_slots = janice_day + richard_day
        busy_slots.sort(key=lambda x: x[1])
        
        # Initialize previous end time to start of work day
        prev_end = start_hour * 60
        
        # Check gaps between busy slots
        for slot in busy_slots:
            slot_start = slot[1] * 60
            if slot_start - prev_end >= duration:
                # Found a gap
                start_time = prev_end
                end_time = start_time + duration
                return f"{int(start_time//60):02d}:{int(start_time%60):02d}:{int(end_time//60):02d}:{int(end_time%60):02d}"
            prev_end = max(prev_end, slot[2] * 60)
        
        # Check after last busy slot
        if (end_hour * 60) - prev_end >= duration:
            start_time = prev_end
            end_time = start_time + duration
            return f"{int(start_time//60):02d}:{int(start_time%60):02d}:{int(end_time//60):02d}:{int(end_time%60):02d}"
    
    return "No meeting time found"

# Define busy slots for Janice and Richard
janice_busy = [
    ('Monday', 11.5, 12.0),
    ('Tuesday', 9.5, 10.0),
    ('Tuesday', 14.5, 15.0),
    ('Wednesday', 11.0, 11.5),
    ('Wednesday', 13.5, 14.0),
    ('Thursday', 15.5, 16.0),
    ('Friday', 13.5, 14.0),
    ('Friday', 16.0, 16.5)
]

richard_busy = [
    ('Monday', 9.0, 10.5),
    ('Monday', 12.5, 13.5),
    ('Monday', 14.0, 14.5),
    ('Monday', 15.0, 15.5),
    ('Tuesday', 9.5, 10.0),
    ('Tuesday', 10.5, 11.0),
    ('Tuesday', 12.0, 13.0),
    ('Tuesday', 14.0, 14.5),
    ('Tuesday', 15.5, 16.0),
    ('Tuesday', 16.5, 17.0),
    ('Wednesday', 9.0, 12.0),
    ('Wednesday', 13.0, 13.5),
    ('Wednesday', 14.0, 16.0),
    ('Thursday', 9.0, 10.0),
    ('Thursday', 10.5, 11.5),
    ('Thursday', 12.0, 12.5),
    ('Thursday', 13.0, 14.5),
    ('Thursday', 15.0, 15.5),
    ('Thursday', 16.0, 17.0),
    ('Friday', 9.0, 17.0)
]

work_hours = (9.0, 17.0)
duration = 30  # minutes

print(find_meeting_time(janice_busy, richard_busy, work_hours, duration))