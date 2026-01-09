from constraint import Problem

def main():
    # Define the problem
    problem = Problem()
    
    # Work hours: 9:00 to 17:00 (9:00 AM to 5:00 PM)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Meeting duration: 30 minutes
    meeting_duration = 30
    
    # Samuel's busy times in minutes from midnight
    samuel_busy = [
        (9 * 60, 10 * 60 + 30),    # 9:00-10:30
        (11 * 60 + 30, 12 * 60),   # 11:30-12:00
        (13 * 60, 13 * 60 + 30),   # 13:00-13:30
        (14 * 60, 16 * 60),        # 14:00-16:00
        (16 * 60 + 30, 17 * 60)    # 16:30-17:00
    ]
    
    # Convert busy times to available time slots
    available_slots = []
    current_time = work_start
    
    # Sort busy times by start time
    samuel_busy.sort()
    
    for busy_start, busy_end in samuel_busy:
        if current_time < busy_start:
            # Add available slot before this busy period
            available_slots.append((current_time, busy_start))
        current_time = max(current_time, busy_end)
    
    # Add remaining time after last busy period
    if current_time < work_end:
        available_slots.append((current_time, work_end))
    
    # Find the earliest available slot that fits the meeting
    meeting_start = None
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= meeting_duration:
            meeting_start = slot_start
            break
    
    if meeting_start is None:
        print("No available time slot found")
        return
    
    # Convert meeting time back to readable format
    start_hour = meeting_start // 60
    start_minute = meeting_start % 60
    end_time = meeting_start + meeting_duration
    end_hour = end_time // 60
    end_minute = end_time % 60
    
    # Format the output
    time_range = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
    day_of_week = "Monday"
    
    print(f"{time_range}")
    print(f"{day_of_week}")

if __name__ == "__main__":
    main()