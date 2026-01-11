def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Tuesday schedules in minutes from midnight
    # Daniel's Tuesday busy times
    daniel_busy_tuesday = [
        (11*60, 12*60),      # 11:00-12:00
        (13*60, 13*60+30),   # 13:00-13:30
        (15*60+30, 16*60),   # 15:30-16:00
        (16*60+30, 17*60)    # 16:30-17:00
    ]
    
    # Bradley's Tuesday busy times
    bradley_busy_tuesday = [
        (10*60+30, 11*60),   # 10:30-11:00
        (12*60, 13*60),      # 12:00-13:00
        (13*60+30, 14*60),   # 13:30-14:00
        (15*60+30, 16*60+30) # 15:30-16:30
    ]
    
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Bradley doesn't want to meet before 12:00 on Tuesday
    # So we start checking from 12:00
    start_check = 12 * 60
    
    # Check all possible start times from 12:00 to 16:30 (since meeting is 30 min)
    for start_time in range(start_check, work_end - meeting_duration + 1, 15):  # Check every 15 minutes
        end_time = start_time + meeting_duration
        
        # Check if this slot conflicts with Daniel's schedule
        daniel_conflict = False
        for busy_start, busy_end in daniel_busy_tuesday:
            if not (end_time <= busy_start or start_time >= busy_end):
                daniel_conflict = True
                break
        
        if daniel_conflict:
            continue
        
        # Check if this slot conflicts with Bradley's schedule
        bradley_conflict = False
        for busy_start, busy_end in bradley_busy_tuesday:
            if not (end_time <= busy_start or start_time >= busy_end):
                bradley_conflict = True
                break
        
        if bradley_conflict:
            continue
        
        # Found a valid slot
        # Convert back to HH:MM format
        start_hour = start_time // 60
        start_minute = start_time % 60
        end_hour = end_time // 60
        end_minute = end_time % 60
        
        return "Tuesday", f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
    
    return None, None

def main():
    day, time_slot = find_meeting_time()
    
    if day and time_slot:
        print(f"Meeting scheduled for {day} at {time_slot}")
    else:
        print("No suitable meeting time found")

if __name__ == "__main__":
    main()