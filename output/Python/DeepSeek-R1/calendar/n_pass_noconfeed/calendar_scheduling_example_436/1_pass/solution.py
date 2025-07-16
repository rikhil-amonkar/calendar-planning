def main():
    work_start = 9 * 60  # 540 minutes (9:00)
    work_end = 17 * 60   # 1020 minutes (17:00)
    meeting_duration = 30  # minutes

    # List all busy intervals in minutes (start, end)
    busy_intervals = []
    
    # Patrick
    busy_intervals.append((13*60+30, 14*60))    # 13:30-14:00
    busy_intervals.append((14*60+30, 15*60))     # 14:30-15:00
    
    # Shirley
    busy_intervals.append((9*60, 9*60+30))       # 9:00-9:30
    busy_intervals.append((11*60, 11*60+30))     # 11:00-11:30
    busy_intervals.append((12*60, 12*60+30))     # 12:00-12:30
    busy_intervals.append((14*60+30, 15*60))     # 14:30-15:00
    busy_intervals.append((16*60, 17*60))        # 16:00-17:00
    
    # Jeffrey
    busy_intervals.append((9*60, 9*60+30))       # 9:00-9:30
    busy_intervals.append((10*60+30, 11*60))     # 10:30-11:00
    busy_intervals.append((11*60+30, 12*60))     # 11:30-12:00
    busy_intervals.append((13*60, 13*60+30))     # 13:00-13:30
    busy_intervals.append((16*60, 17*60))        # 16:00-17:00
    
    # Gloria
    busy_intervals.append((11*60+30, 12*60))     # 11:30-12:00
    busy_intervals.append((15*60, 15*60+30))     # 15:00-15:30
    
    # Nathan
    busy_intervals.append((9*60, 9*60+30))       # 9:00-9:30
    busy_intervals.append((10*60+30, 12*60))     # 10:30-12:00
    busy_intervals.append((14*60, 17*60))        # 14:00-17:00
    
    # Angela
    busy_intervals.append((9*60, 9*60+30))       # 9:00-9:30
    busy_intervals.append((10*60, 11*60))        # 10:00-11:00
    busy_intervals.append((12*60+30, 15*60))     # 12:30-15:00
    busy_intervals.append((15*60+30, 16*60+30))  # 15:30-16:30
    
    # David
    busy_intervals.append((9*60, 9*60+30))       # 9:00-9:30
    busy_intervals.append((10*60, 10*60+30))     # 10:00-10:30
    busy_intervals.append((11*60, 14*60))        # 11:00-14:00
    busy_intervals.append((14*60+30, 16*60+30))  # 14:30-16:30
    
    # Merge overlapping intervals
    busy_intervals.sort(key=lambda x: x[0])
    merged = []
    for interval in busy_intervals:
        if not merged:
            merged.append(list(interval))
        else:
            last = merged[-1]
            if interval[0] <= last[1]:
                last[1] = max(last[1], interval[1])
            else:
                merged.append(list(interval))
    
    # Calculate free intervals within work hours
    free_intervals = []
    current = work_start
    for start, end in merged:
        if current < start:
            free_intervals.append((current, start))
            current = end
        else:
            if end > current:
                current = end
    if current < work_end:
        free_intervals.append((current, work_end))
    
    # Find the first free interval that can fit the meeting
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            # Convert to HH:MM format
            start_hour = meeting_start // 60
            start_min = meeting_start % 60
            end_hour = meeting_end // 60
            end_min = meeting_end % 60
            # Format as HH:MM:HH:MM and day
            print(f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d} Monday")
            return
    
    # If no slot found (though problem states there is one)
    print("No suitable time found Monday")

if __name__ == "__main__":
    main()