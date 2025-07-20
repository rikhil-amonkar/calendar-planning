def main():
    # Convert work hours to minutes
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 60  # 60 minutes

    # Busy intervals for each participant (in minutes)
    busy_intervals = []
    
    # Joshua's busy intervals
    busy_intervals.append((11*60, 12*60+30))      # 11:00-12:30
    busy_intervals.append((13*60+30, 14*60+30))   # 13:30-14:30
    busy_intervals.append((16*60+30, 17*60))      # 16:30-17:00
    
    # Jerry's busy intervals
    busy_intervals.append((9*60, 9*60+30))        # 9:00-9:30
    busy_intervals.append((10*60+30, 12*60))      # 10:30-12:00
    busy_intervals.append((12*60+30, 13*60))      # 12:30-13:00
    busy_intervals.append((13*60+30, 14*60))      # 13:30-14:00
    busy_intervals.append((14*60+30, 15*60))      # 14:30-15:00
    busy_intervals.append((15*60+30, 16*60))      # 15:30-16:00
    
    # Jesse's busy intervals
    busy_intervals.append((9*60, 9*60+30))        # 9:00-9:30
    busy_intervals.append((10*60+30, 12*60))      # 10:30-12:00
    busy_intervals.append((12*60+30, 13*60))      # 12:30-13:00
    busy_intervals.append((14*60+30, 15*60))      # 14:30-15:00
    busy_intervals.append((15*60+30, 16*60+30))   # 15:30-16:30
    
    # Kenneth's busy intervals
    busy_intervals.append((10*60+30, 12*60+30))   # 10:30-12:30
    busy_intervals.append((13*60+30, 14*60))       # 13:30-14:00
    busy_intervals.append((14*60+30, 15*60))       # 14:30-15:00
    busy_intervals.append((15*60+30, 16*60))       # 15:30-16:00
    busy_intervals.append((16*60+30, 17*60))       # 16:30-17:00

    # Sort busy intervals by start time
    busy_intervals.sort(key=lambda x: x[0])
    
    # Merge overlapping busy intervals
    merged = []
    if busy_intervals:
        current_start, current_end = busy_intervals[0]
        for interval in busy_intervals[1:]:
            if interval[0] <= current_end:
                current_end = max(current_end, interval[1])
            else:
                merged.append((current_start, current_end))
                current_start, current_end = interval
        merged.append((current_start, current_end))
    
    # Find free intervals within work hours
    free_intervals = []
    prev_end = work_start
    for start, end in merged:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))
    
    # Find the first free interval that can fit the meeting
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            # Convert back to HH:MM format
            start_hour = meeting_start // 60
            start_min = meeting_start % 60
            end_hour = meeting_end // 60
            end_min = meeting_end % 60
            print(f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}")
            print("Monday")
            return
    
    # If no slot found (though problem states there is a solution)
    print("No suitable time found")

if __name__ == "__main__":
    main()