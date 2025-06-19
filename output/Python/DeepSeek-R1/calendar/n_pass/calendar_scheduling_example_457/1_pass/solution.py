def main():
    # Work hours: 9:00 to 17:00 -> 0 to 480 minutes
    work_start = 0
    work_end = 480
    meeting_duration = 30

    # List to collect all busy intervals in minutes (relative to 9:00)
    busy_intervals = []
    
    # Andrea
    busy_intervals.append((30, 90))    # 9:30-10:30
    busy_intervals.append((210, 270))   # 13:30-14:30
    
    # Ruth
    busy_intervals.append((210, 240))   # 12:30-13:00? Actually, 12:30 is 210, 13:00 is 240 -> but 210 to 240
    
    # Steven
    busy_intervals.append((60, 90))     # 10:00-10:30
    busy_intervals.append((120, 150))   # 11:00-11:30
    busy_intervals.append((180, 210))   # 12:00-12:30
    busy_intervals.append((270, 300))   # 13:30-14:00
    busy_intervals.append((360, 420))   # 15:00-16:00
    
    # Grace: none
    
    # Kyle
    busy_intervals.append((0, 30))      # 9:00-9:30
    busy_intervals.append((90, 180))    # 10:30-12:00
    busy_intervals.append((210, 240))   # 12:30-13:00
    busy_intervals.append((270, 360))   # 13:30-15:00
    busy_intervals.append((390, 420))   # 15:30-16:00
    busy_intervals.append((450, 480))   # 16:30-17:00
    
    # Elijah
    busy_intervals.append((0, 120))     # 9:00-11:00
    busy_intervals.append((150, 240))   # 11:30-13:00
    busy_intervals.append((270, 300))   # 13:30-14:00
    busy_intervals.append((390, 420))   # 15:30-16:00
    busy_intervals.append((450, 480))   # 16:30-17:00
    
    # Lori
    busy_intervals.append((0, 30))      # 9:00-9:30
    busy_intervals.append((60, 150))    # 10:00-11:30
    busy_intervals.append((180, 270))   # 12:00-13:30
    busy_intervals.append((300, 420))   # 14:00-16:00
    busy_intervals.append((450, 480))   # 16:30-17:00

    # Sort busy intervals by start time
    busy_intervals.sort(key=lambda x: x[0])
    
    # Merge intervals
    merged = []
    for interval in busy_intervals:
        if not merged:
            merged.append(interval)
        else:
            last = merged[-1]
            if interval[0] <= last[1]:
                merged[-1] = (last[0], max(last[1], interval[1]))
            else:
                merged.append(interval)
    
    # Find free intervals
    free_intervals = []
    current_start = work_start
    for interval in merged:
        if current_start < interval[0]:
            free_intervals.append((current_start, interval[0]))
        current_start = max(current_start, interval[1])
    if current_start < work_end:
        free_intervals.append((current_start, work_end))
    
    # Find the first free interval that can fit the meeting
    meeting_start = None
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            break
    
    if meeting_start is None:
        print("No suitable time found")
        return
    
    meeting_end = meeting_start + meeting_duration
    
    # Convert minutes to time string
    def min_to_time(total_minutes):
        hour = 9 + total_minutes // 60
        minute = total_minutes % 60
        return hour, minute
    
    start_hour, start_minute = min_to_time(meeting_start)
    end_hour, end_minute = min_to_time(meeting_end)
    
    # Format the time string as HH:MM:HH:MM
    time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
    
    print("Monday")
    print(time_str)

if __name__ == "__main__":
    main()