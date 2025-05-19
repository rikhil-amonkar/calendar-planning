from datetime import datetime, timedelta

def find_meeting_time():
    # Define work hours
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    meeting_duration = timedelta(minutes=30)
    
    # Days to consider
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    
    # Eugene's busy slots
    eugene_busy = {
        "Monday": [
            ("11:00", "12:00"), ("13:30", "14:00"), ("14:30", "15:00"), ("16:00", "16:30")
        ],
        "Wednesday": [
            ("09:00", "09:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:30", "15:00")
        ],
        "Thursday": [
            ("09:30", "10:00"), ("11:00", "12:30")
        ],
        "Friday": [
            ("10:30", "11:00"), ("12:00", "12:30"), ("13:00", "13:30")
        ]
    }
    
    # Eric's busy slots
    eric_busy = {
        "Monday": [("09:00", "17:00")],
        "Tuesday": [("09:00", "17:00")],
        "Wednesday": [
            ("09:00", "11:30"), ("12:00", "14:00"), ("14:30", "16:30")
        ],
        "Thursday": [("09:00", "17:00")],
        "Friday": [
            ("09:00", "11:00"), ("11:30", "17:00")
        ]
    }
    
    # Iterate through each day (excluding Wednesday first due to Eric's preference)
    preferred_days = [day for day in days if day != "Wednesday"] + ["Wednesday"]
    
    for day in preferred_days:
        # Collect all busy slots for both participants
        busy_slots = []
        
        # Add Eugene's busy slots
        for slot in eugene_busy.get(day, []):
            start = datetime.strptime(slot[0], "%H:%M")
            end = datetime.strptime(slot[1], "%H:%M")
            busy_slots.append((start, end))
        
        # Add Eric's busy slots
        for slot in eric_busy.get(day, []):
            start = datetime.strptime(slot[0], "%H:%M")
            end = datetime.strptime(slot[1], "%H:%M")
            busy_slots.append((start, end))
        
        # Sort busy slots by start time
        busy_slots.sort()
        
        # Find available slots
        available_slots = []
        prev_end = work_start
        
        for slot in busy_slots:
            slot_start, slot_end = slot
            if slot_start > prev_end:
                available_slots.append((prev_end, slot_start))
            prev_end = max(prev_end, slot_end)
        
        if prev_end < work_end:
            available_slots.append((prev_end, work_end))
        
        # Check each available slot for sufficient duration
        for slot in available_slots:
            slot_start, slot_end = slot
            if slot_end - slot_start >= meeting_duration:
                meeting_start = slot_start
                meeting_end = meeting_start + meeting_duration
                # Format the output
                start_str = meeting_start.strftime("%H:%M")
                end_str = meeting_end.strftime("%H:%M")
                print(f"{day}: {start_str}:{end_str}")
                return
    
    print("No suitable time found.")

find_meeting_time()