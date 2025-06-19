def main():
    # Work hours: 9:00 to 17:00 (converted to minutes from 9:00)
    work_start = 0    # 9:00
    work_end = 480    # 17:00 (8 hours * 60 minutes)
    meeting_duration = 30  # minutes

    # Collect all busy intervals (each as [start_minute, end_minute])
    busy_intervals = []
    
    # Gregory's schedule
    busy_intervals.append([0, 60])     # 9:00-10:00
    busy_intervals.append([90, 150])   # 10:30-11:30
    busy_intervals.append([210, 240])  # 12:30-13:00
    busy_intervals.append([270, 300])  # 13:30-14:00

    # Christine's schedule
    busy_intervals.append([0, 150])    # 9:00-11:30
    busy_intervals.append([270, 480])  # 13:30-17:00

    # Vincent's schedule
    busy_intervals.append([0, 30])     # 9:00-9:30
    busy_intervals.append([90, 180])   # 10:30-12:00
    busy_intervals.append([210, 300])  # 12:30-14:00
    busy_intervals.append([330, 480])  # 14:30-17:00
    
    # Natalie has no meetings

    # Merge overlapping busy intervals
    if not busy_intervals:
        merged = []
    else:
        busy_intervals.sort(key=lambda x: x[0])
        merged = []
        current_start, current_end = busy_intervals[0]
        for interval in busy_intervals[1:]:
            if interval[0] <= current_end:
                current_end = max(current_end, interval[1])
            else:
                merged.append([current_start, current_end])
                current_start, current_end = interval
        merged.append([current_start, current_end])

    # Find free intervals within work hours
    free_intervals = []
    if not merged:
        free_intervals.append([work_start, work_end])
    else:
        # Before first busy interval
        if merged[0][0] > work_start:
            free_intervals.append([work_start, merged[0][0]])
        
        # Between busy intervals
        for i in range(len(merged) - 1):
            gap_start = merged[i][1]
            gap_end = merged[i+1][0]
            if gap_start < gap_end:
                free_intervals.append([gap_start, gap_end])
                
        # After last busy interval
        if merged[-1][1] < work_end:
            free_intervals.append([merged[-1][1], work_end])

    # Find the first free interval that can fit the meeting
    slot = None
    for interval in free_intervals:
        start_min, end_min = interval
        if end_min - start_min >= meeting_duration:
            slot = [start_min, start_min + meeting_duration]
            break

    # Convert slot to time string (HH:MM)
    def minutes_to_time(minutes):
        hour = 9 + minutes // 60
        minute = minutes % 60
        return f"{hour:02d}:{minute:02d}"

    start_time_str = minutes_to_time(slot[0])
    end_time_str = minutes_to_time(slot[1])
    time_range_str = f"{start_time_str}:{end_time_str}"
    
    print(time_range_str)
    print("Monday")

if __name__ == "__main__":
    main()