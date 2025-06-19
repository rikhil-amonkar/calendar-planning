def main():
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    duration = 30        # Meeting duration in minutes

    # Busy intervals for all participants (each interval is [start_minute, end_minute])
    busy = [
        # Diane
        [9*60+30, 10*60],      # 9:30-10:00
        [14*60+30, 15*60],     # 14:30-15:00
        # Jack
        [13*60+30, 14*60],     # 13:30-14:00
        [14*60+30, 15*60],     # 14:30-15:00
        # Eugene
        [9*60, 10*60],         # 9:00-10:00
        [10*60+30, 11*60+30],  # 10:30-11:30
        [12*60, 14*60+30],     # 12:00-14:30
        [15*60, 16*60+30],     # 15:00-16:30
        # Patricia
        [9*60+30, 10*60+30],  # 9:30-10:30
        [11*60, 12*60],        # 11:00-12:00
        [12*60+30, 14*60],     # 12:30-14:00
        [15*60, 16*60+30]      # 15:00-16:30
    ]

    # Sort busy intervals by start time
    busy.sort(key=lambda x: x[0])
    
    # Merge overlapping or adjacent intervals
    merged_busy = []
    for interval in busy:
        if not merged_busy:
            merged_busy.append(interval)
        else:
            last_interval = merged_busy[-1]
            if interval[0] <= last_interval[1]:
                last_interval[1] = max(last_interval[1], interval[1])
            else:
                merged_busy.append(interval)
    
    # Find free intervals within work hours
    free_intervals = []
    
    # Check before the first busy interval
    first_start = merged_busy[0][0]
    if first_start - work_start >= duration:
        free_intervals.append([work_start, first_start])
    
    # Check between busy intervals
    for i in range(len(merged_busy) - 1):
        gap_start = merged_busy[i][1]
        gap_end = merged_busy[i+1][0]
        if gap_end - gap_start >= duration:
            free_intervals.append([gap_start, gap_end])
    
    # Check after the last busy interval
    last_end = merged_busy[-1][1]
    if work_end - last_end >= duration:
        free_intervals.append([last_end, work_end])
    
    # Select the first free interval that fits the meeting duration
    if free_intervals:
        start_minutes = free_intervals[0][0]
        end_minutes = start_minutes + duration
        
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print("Monday")
        print(time_str)
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()