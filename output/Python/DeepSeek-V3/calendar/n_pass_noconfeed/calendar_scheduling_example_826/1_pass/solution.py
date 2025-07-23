from datetime import datetime, timedelta

def find_meeting_time():
    # Define work hours and days to consider
    work_start = datetime.strptime("09:00", "%H:%M").time()
    work_end = datetime.strptime("17:00", "%H:%M").time()
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    
    # Cheryl's preferences: avoid Wednesday and Thursday
    preferred_days = ["Monday", "Tuesday"]
    
    # James's schedule: each day's busy slots
    james_schedule = {
        "Monday": ["09:00-09:30", "10:30-11:00", "12:30-13:00", "14:30-15:30", "16:30-17:00"],
        "Tuesday": ["09:00-11:00", "11:30-12:00", "12:30-15:30", "16:00-17:00"],
        "Wednesday": ["10:00-11:00", "12:00-13:00", "13:30-16:00"],
        "Thursday": ["09:30-11:30", "12:00-12:30", "13:00-13:30", "14:00-14:30", "16:30-17:00"]
    }
    
    meeting_duration = timedelta(minutes=30)
    
    # Convert James's schedule to datetime.time objects for easier comparison
    james_busy = {}
    for day in days:
        busy_slots = []
        for slot in james_schedule[day]:
            start, end = slot.split('-')
            start_time = datetime.strptime(start, "%H:%M").time()
            end_time = datetime.strptime(end, "%H:%M").time()
            busy_slots.append((start_time, end_time))
        james_busy[day] = busy_slots
    
    # Check preferred days first (Monday, Tuesday)
    for day in preferred_days:
        busy_slots = james_busy[day]
        # Start checking from the beginning of the work day
        current_time = work_start
        
        while True:
            # Calculate potential end time
            end_time = (datetime.combine(datetime.today(), current_time) + meeting_duration).time()
            
            # Check if end time exceeds work hours
            if end_time > work_end:
                break
            
            # Check if current_time to end_time is free
            conflict = False
            for busy_start, busy_end in busy_slots:
                if (current_time < busy_end) and (end_time > busy_start):
                    conflict = True
                    break
            
            if not conflict:
                # Found a suitable slot
                return day, current_time, end_time
            
            # Move to the next possible start time (increment by 30 minutes)
            current_time = (datetime.combine(datetime.today(), current_time) + timedelta(minutes=30)).time()
    
    # If no slot found in preferred days, check other days (though Cheryl prefers not)
    for day in ["Wednesday", "Thursday"]:
        busy_slots = james_busy[day]
        current_time = work_start
        
        while True:
            end_time = (datetime.combine(datetime.today(), current_time) + meeting_duration).time()
            
            if end_time > work_end:
                break
            
            conflict = False
            for busy_start, busy_end in busy_slots:
                if (current_time < busy_end) and (end_time > busy_start):
                    conflict = True
                    break
            
            if not conflict:
                return day, current_time, end_time
            
            current_time = (datetime.combine(datetime.today(), current_time) + timedelta(minutes=30)).time()
    
    return None

# Find and print the meeting time
day, start_time, end_time = find_meeting_time()
start_str = start_time.strftime("%H:%M")
end_str = end_time.strftime("%H:%M")
print(f"{day}: {start_str}:{end_str}")