from datetime import datetime, timedelta

def find_meeting_time():
    # Define work hours and days to consider
    work_start = datetime.strptime("09:00", "%H:%M").time()
    work_end = datetime.strptime("17:00", "%H:%M").time()
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    
    # Define busy times for each participant per day
    carl_busy = {
        "Monday": [("11:00", "11:30")],
        "Tuesday": [("14:30", "15:00")],
        "Wednesday": [("10:00", "11:30"), ("13:00", "13:30")],
        "Thursday": [("13:30", "14:00"), ("16:00", "16:30")]
    }
    
    margaret_busy = {
        "Monday": [("09:00", "10:30"), ("11:00", "17:00")],
        "Tuesday": [("09:30", "12:00"), ("13:30", "14:00"), ("15:30", "17:00")],
        "Wednesday": [("09:30", "12:00"), ("12:30", "13:00"), ("13:30", "14:30"), ("15:00", "17:00")],
        "Thursday": [("10:00", "12:00"), ("12:30", "14:00"), ("14:30", "17:00")]
    }
    
    # Convert busy times to datetime.time for easier comparison
    def parse_busy_times(busy_dict):
        parsed = {}
        for day, slots in busy_dict.items():
            parsed[day] = []
            for start, end in slots:
                start_time = datetime.strptime(start, "%H:%M").time()
                end_time = datetime.strptime(end, "%H:%M").time()
                parsed[day].append((start_time, end_time))
        return parsed
    
    carl_busy_parsed = parse_busy_times(carl_busy)
    margaret_busy_parsed = parse_busy_times(margaret_busy)
    
    # Check if a time slot is available for both participants
    def is_available(day, start_time, end_time):
        # Check Carl's availability
        for busy_start, busy_end in carl_busy_parsed.get(day, []):
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        # Check Margaret's availability
        for busy_start, busy_end in margaret_busy_parsed.get(day, []):
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        return True
    
    # Iterate through each day (excluding Thursday first due to Carl's preference)
    preferred_days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    # Move Thursday to the end of the list to prioritize other days
    preferred_days.remove("Thursday")
    preferred_days.append("Thursday")
    
    meeting_duration = timedelta(hours=1)
    time_slot = timedelta(minutes=30)  # Check every 30 minutes
    
    for day in preferred_days:
        current_time = datetime.combine(datetime.today(), work_start)
        end_time = datetime.combine(datetime.today(), work_end)
        
        while current_time + meeting_duration <= end_time:
            slot_start = current_time.time()
            slot_end = (current_time + meeting_duration).time()
            
            if is_available(day, slot_start, slot_end):
                # Format the output as HH:MM:HH:MM
                start_str = slot_start.strftime("%H:%M")
                end_str = slot_end.strftime("%H:%M")
                print(f"{day}: {start_str}:{end_str}")
                return
            
            current_time += time_slot
    
    print("No suitable time found.")

find_meeting_time()