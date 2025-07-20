def main():
    # Define work hours (9:00 to 17:00) in minutes from 9:00
    work_start = 0    # 9:00
    work_end = 480    # 17:00 (8*60=480)
    
    # Collect all busy intervals (start, end) in minutes (end is exclusive)
    busy_intervals = []
    
    # Kimberly's meetings
    busy_intervals.append((60, 90))    # 10:00-10:30
    busy_intervals.append((120, 180))  # 11:00-12:00
    busy_intervals.append((420, 450))  # 16:00-16:30
    
    # Marie's meetings
    busy_intervals.append((60, 120))   # 10:00-11:00
    busy_intervals.append((150, 360))  # 11:30-15:00
    busy_intervals.append((420, 450))  # 16:00-16:30
    
    # Diana's meetings
    busy_intervals.append((30, 60))    # 9:30-10:00
    busy_intervals.append((90, 330))   # 10:30-14:30
    busy_intervals.append((390, 480))  # 15:30-17:00
    
    # Sort intervals by start time
    busy_intervals.sort(key=lambda x: x[0])
    
    # Merge overlapping intervals
    merged = []
    if busy_intervals:
        current_start, current_end = busy_intervals[0]
        for i in range(1, len(busy_intervals)):
            s, e = busy_intervals[i]
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))
    
    # Find free intervals
    free_intervals = []
    if not merged:
        free_intervals.append((work_start, work_end))
    else:
        # Before first meeting
        if work_start < merged[0][0]:
            free_intervals.append((work_start, merged[0][0]))
        # Between meetings
        for i in range(len(merged) - 1):
            free_start = merged[i][1]
            free_end = merged[i+1][0]
            if free_start < free_end:
                free_intervals.append((free_start, free_end))
        # After last meeting
        if merged[-1][1] < work_end:
            free_intervals.append((merged[-1][1], work_end))
    
    # Find a 30-minute slot starting at or after 10:00 (60 minutes)
    candidate_start = None
    for s, e in free_intervals:
        start_time = max(s, 60)  # Avoid before 10:00
        if start_time + 30 <= e:
            candidate_start = start_time
            break
    # Fallback: if no slot after 10:00, take first available
    if candidate_start is None:
        for s, e in free_intervals:
            if e - s >= 30:
                candidate_start = s
                break
    
    # Convert start and end times to HH:MM format
    start_min = candidate_start
    end_min = candidate_start + 30
    
    # Calculate absolute hours and minutes
    start_hour = 9 + start_min // 60
    start_minute = start_min % 60
    end_hour = 9 + end_min // 60
    end_minute = end_min % 60
    
    # Format as HH:MM with leading zeros
    start_str = f"{start_hour:02d}:{start_minute:02d}"
    end_str = f"{end_hour:02d}:{end_minute:02d}"
    
    # Output day and time range
    print("Monday")
    print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()