def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Convert busy times to minutes since midnight
    # Each busy period is (start_minutes, end_minutes)
    busy_times = {
        "Walter": [],  # No meetings
        "Cynthia": [
            (9*60, 9*60+30),    # 9:00-9:30
            (10*60, 10*60+30),  # 10:00-10:30
            (13*60+30, 14*60+30),  # 13:30-14:30
            (15*60, 16*60)      # 15:00-16:00
        ],
        "Ann": [
            (10*60, 11*60),      # 10:00-11:00
            (13*60, 13*60+30),   # 13:00-13:30
            (14*60, 15*60),      # 14:00-15:00
            (16*60, 16*60+30)    # 16:00-16:30
        ],
        "Catherine": [
            (9*60, 11*60+30),    # 9:00-11:30
            (12*60+30, 13*60+30), # 12:30-13:30
            (14*60+30, 17*60)    # 14:30-17:00
        ],
        "Kyle": [
            (9*60, 9*60+30),     # 9:00-9:30
            (10*60, 11*60+30),   # 10:00-11:30
            (12*60, 12*60+30),   # 12:00-12:30
            (13*60, 14*60+30),   # 13:00-14:30
            (15*60, 16*60)       # 15:00-16:00
        ]
    }
    
    # Check every minute from work_start to work_end - 30 minutes
    for start_minute in range(work_start, work_end - 30 + 1):
        end_minute = start_minute + 30
        slot_available = True
        
        # Check if this slot conflicts with anyone's busy time
        for person, busy_periods in busy_times.items():
            person_free = True
            for busy_start, busy_end in busy_periods:
                # Check if the proposed slot overlaps with any busy period
                if not (end_minute <= busy_start or start_minute >= busy_end):
                    person_free = False
                    break
            
            if not person_free:
                slot_available = False
                break
        
        if slot_available:
            # Convert minutes back to HH:MM format
            start_hour = start_minute // 60
            start_min = start_minute % 60
            end_hour = end_minute // 60
            end_min = end_minute % 60
            
            return f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
    
    return None

def main():
    meeting_time = find_meeting_time()
    if meeting_time:
        print(f"Monday:{meeting_time}")
    else:
        print("No available time slot found")

if __name__ == "__main__":
    main()