def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def main():
    work_start = 540  # 9:00 in minutes
    work_end = 1020    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Samuel's schedule: each day has list of busy time ranges as strings
    samuel_schedule = {
        'Monday': ["10:30-11:00", "12:00-12:30", "13:00-15:00", "15:30-16:30"],
        'Tuesday': ["9:00-12:00", "14:00-15:30", "16:30-17:00"],
        'Wednesday': ["10:30-11:00", "11:30-12:00", "12:30-13:00", "14:00-14:30", "15:00-16:00"]
    }
    
    for day in days:
        busy_intervals = []
        # Process Samuel's busy intervals for the current day
        if day in samuel_schedule:
            for time_range in samuel_schedule[day]:
                start_str, end_str = time_range.split('-')
                start_min = time_to_minutes(start_str)
                end_min = time_to_minutes(end_str)
                busy_intervals.append((start_min, end_min))
        
        # Sort busy intervals by start time
        busy_intervals.sort(key=lambda x: x[0])
        
        # Calculate free intervals for Samuel
        free_intervals = []
        current_start = work_start
        
        for s_busy, e_busy in busy_intervals:
            if current_start < s_busy:
                # Add free interval from current_start to start of busy block
                free_intervals.append((current_start, s_busy))
            current_start = max(current_start, e_busy)
        
        # Add remaining free interval after last busy block if any
        if current_start < work_end:
            free_intervals.append((current_start, work_end))
        
        # Find the first free slot of at least 30 minutes
        for start_free, end_free in free_intervals:
            duration = end_free - start_free
            if duration >= 30:
                meeting_start = start_free
                meeting_end = meeting_start + 30
                
                # Format meeting times
                start_hour = meeting_start // 60
                start_min = meeting_start % 60
                end_hour = meeting_end // 60
                end_min = meeting_end % 60
                
                # Output day and time in HH:MM:HH:MM format
                print(day)
                print(f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}")
                return
    
    # Fallback in case no slot is found (though problem guarantees a solution)
    print("No suitable time found")

if __name__ == "__main__":
    main()