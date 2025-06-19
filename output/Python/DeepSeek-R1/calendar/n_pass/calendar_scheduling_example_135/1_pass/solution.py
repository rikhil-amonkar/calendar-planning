def main():
    work_start = 540   # 9:00 in minutes
    work_end = 1020     # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Define busy intervals for each participant in minutes (start, end)
    eric_busy = []
    ashley_busy = [(10*60, 10*60+30), (11*60, 12*60), (12*60+30, 13*60), (15*60, 16*60)]
    ronald_busy = [(9*60, 9*60+30), (10*60, 11*60+30), (12*60+30, 14*60), (14*60+30, 17*60)]
    larry_busy = [(9*60, 12*60), (13*60, 17*60)]

    # Combine all busy intervals
    all_busy = eric_busy + ashley_busy + ronald_busy + larry_busy

    # If there are no busy intervals, the entire work day is free
    if not all_busy:
        if work_end - work_start >= meeting_duration:
            start_time_minutes = work_start
        else:
            # According to the problem, a solution exists, so this may not be needed
            start_time_minutes = None
    else:
        # Sort busy intervals by start time
        all_busy.sort(key=lambda x: x[0])
        
        # Merge overlapping or adjacent intervals
        merged = []
        current_start, current_end = all_busy[0]
        for i in range(1, len(all_busy)):
            interval = all_busy[i]
            if interval[0] <= current_end:
                if interval[1] > current_end:
                    current_end = interval[1]
            else:
                merged.append((current_start, current_end))
                current_start, current_end = interval
        merged.append((current_start, current_end))
        
        # Find free intervals within work hours
        free_intervals = []
        # Before first busy interval
        if merged[0][0] > work_start:
            free_intervals.append((work_start, merged[0][0]))
        
        # Between busy intervals
        for i in range(1, len(merged)):
            prev_end = merged[i-1][1]
            curr_start = merged[i][0]
            if curr_start > prev_end:
                free_intervals.append((prev_end, curr_start))
        
        # After last busy interval
        if merged[-1][1] < work_end:
            free_intervals.append((merged[-1][1], work_end))
        
        # Find the first free interval that can fit the meeting
        start_time_minutes = None
        for interval in free_intervals:
            start, end = interval
            if end - start >= meeting_duration:
                start_time_minutes = start
                break

    # Convert start time to HH:MM and calculate end time
    start_hour = start_time_minutes // 60
    start_minute = start_time_minutes % 60
    end_time_minutes = start_time_minutes + meeting_duration
    end_hour = end_time_minutes // 60
    end_minute = end_time_minutes % 60

    # Format the times as strings
    start_str = f"{start_hour:02d}:{start_minute:02d}"
    end_str = f"{end_hour:02d}:{end_minute:02d}"
    
    # Output the day and time slot in the required format
    print("Monday")
    print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()