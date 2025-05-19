from datetime import datetime, timedelta

def schedule_meeting():
    # Define the meeting duration and timeframe
    meeting_duration = timedelta(minutes=30)
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    # Define the participants' schedules
    randy_schedule = [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
        (datetime.strptime("11:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
        (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M")),
    ]
    
    # Evelyn's preference
    evlyn_preference_end = datetime.strptime("13:00", "%H:%M")
    
    # Define the available slots
    available_slots = []
    
    # Check each hour in the work schedule to find an open slot
    current_time = work_start
    while current_time < work_end:
        slot_start = current_time
        slot_end = current_time + meeting_duration
        
        # Check if the current slot is available
        if slot_end > work_end:
            break
        
        # Check Randy's schedule for conflicts
        available = True
        for start, end in randy_schedule:
            if slot_start < end and slot_end > start:
                available = False
                break
        
        # Check Evelyn's constraint
        if available and slot_end <= evlyn_preference_end:
            available_slots.append((slot_start, slot_end))
        
        current_time += timedelta(minutes=30)  # Increment by 30 minutes
    
    # Assuming there is at least one available slot, we take the first one
    if available_slots:
        start_time, end_time = available_slots[0]
        print(f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')} Monday")
    else:
        print("No available time slots found.")

schedule_meeting()