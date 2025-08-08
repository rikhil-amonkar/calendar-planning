def minutes_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def find_earliest_slot(work_start, work_end, busy_intervals, duration):
    # Start at the beginning of the work day.
    current_time = work_start
    
    # Iterate over busy intervals sorted by start times.
    for busy_start, busy_end in busy_intervals:
        # If there's enough free time before the next busy interval, return that slot.
        if current_time + duration <= busy_start:
            return current_time, current_time + duration
        # Otherwise, move the current time pointer to the end of the busy interval if it's later.
        current_time = max(current_time, busy_end)
    
    # Check for free time after the last busy interval until end of work day.
    if current_time + duration <= work_end:
        return current_time, current_time + duration
    
    # Should never reach here as the problem guarantees a solution.
    return None

def main():
    # Define the day and work hours in minutes.
    day = "Monday"
    work_start = 9 * 60     # 9:00 AM in minutes (540)
    work_end = 17 * 60      # 17:00 PM in minutes (1020)
    meeting_duration = 30   # Meeting duration in minutes
    
    # Define Samuel's unavailable intervals on Monday (in minutes)
    busy_intervals = [
        (9 * 60, 10 * 60 + 30),      # 9:00 to 10:30
        (11 * 60 + 30, 12 * 60),      # 11:30 to 12:00
        (13 * 60, 13 * 60 + 30),      # 13:00 to 13:30
        (14 * 60, 16 * 60),           # 14:00 to 16:00
        (16 * 60 + 30, 17 * 60)       # 16:30 to 17:00
    ]
    
    # Since Andrew and Grace are free all day, only Samuel's schedule matters.
    # Find the earliest available time slot.
    slot = find_earliest_slot(work_start, work_end, busy_intervals, meeting_duration)
    
    if slot:
        start, end = slot
        start_str = minutes_to_str(start)
        end_str = minutes_to_str(end)
        # Output the result in the requested format: HH:MM:HH:MM and day of the week.
        print(f"Meeting is scheduled on {day} from {start_str}:{end_str}")
    else:
        print("No available slot found.")

if __name__ == "__main__":
    main()