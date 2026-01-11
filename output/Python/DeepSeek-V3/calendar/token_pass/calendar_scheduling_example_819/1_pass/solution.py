def find_meeting_time():
    # Work hours
    work_start = 9 * 60   # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    
    # Days to consider
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    
    # Ruth's busy times in minutes since midnight for each day
    ruth_busy = {
        "Monday": [(9*60, 17*60)],
        "Tuesday": [(9*60, 17*60)],
        "Wednesday": [(9*60, 17*60)],
        "Thursday": [(9*60, 11*60), (11*60 + 30, 14*60 + 30), (15*60, 17*60)]
    }
    
    # Julie's preference: avoid Thursday before 11:30
    julie_avoid = ("Thursday", 9*60, 11*60 + 30)
    
    meeting_duration = 30  # minutes
    
    # Check each day
    for day in days:
        # Get Ruth's busy slots for the day
        busy_slots = ruth_busy[day]
        
        # Start checking from work_start to work_end
        current_time = work_start
        
        # Sort busy slots by start time
        busy_sorted = sorted(busy_slots, key=lambda x: x[0])
        
        for busy_start, busy_end in busy_sorted:
            # If there's a gap before this busy slot
            if current_time + meeting_duration <= busy_start:
                # Check Julie's preference for Thursday before 11:30
                if day == julie_avoid[0] and current_time < julie_avoid[2]:
                    # Skip if it's before 11:30 on Thursday
                    if current_time + meeting_duration <= julie_avoid[2]:
                        current_time = busy_end
                        continue
                # If gap is valid, return it
                start_h = current_time // 60
                start_m = current_time % 60
                end_h = (current_time + meeting_duration) // 60
                end_m = (current_time + meeting_duration) % 60
                return day, f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
            # Move current_time to after this busy slot
            if busy_end > current_time:
                current_time = busy_end
        
        # Check after last busy slot until work_end
        if current_time + meeting_duration <= work_end:
            # Check Julie's preference for Thursday before 11:30
            if day == julie_avoid[0] and current_time < julie_avoid[2]:
                if current_time + meeting_duration <= julie_avoid[2]:
                    continue
            start_h = current_time // 60
            start_m = current_time % 60
            end_h = (current_time + meeting_duration) // 60
            end_m = (current_time + meeting_duration) % 60
            return day, f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
    
    return None, None

def main():
    day, time_range = find_meeting_time()
    if day and time_range:
        print(f"{day} {time_range}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()