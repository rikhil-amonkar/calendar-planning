def main():
    # Define work hours (9:00 to 17:00) in minutes
    work_start = 9 * 60  # 540 minutes (9:00)
    work_end = 17 * 60   # 1020 minutes (17:00)
    meeting_duration = 30  # 30 minutes

    # Define schedules for Arthur and Michael (in minutes)
    arthur_schedule = {
        'Monday': [(11*60, 11*60+30), (13*60+30, 14*60), (15*60, 15*60+30)],
        'Wednesday': [(10*60, 10*60+30), (11*60, 11*60+30), (12*60, 12*60+30), (14*60, 14*60+30), (16*60, 16*60+30)]
    }
    
    michael_schedule = {
        'Monday': [(9*60, 12*60), (12*60+30, 13*60), (14*60, 14*60+30), (15*60, 17*60)],
        'Wednesday': [(10*60, 12*60+30), (13*60, 13*60+30)]
    }
    
    # Days to check (skip Tuesday)
    days_to_check = ['Monday', 'Wednesday']
    
    # Iterate over days to find the earliest available slot
    for day in days_to_check:
        # Collect all busy intervals for the day
        busy_intervals = []
        if day in arthur_schedule:
            busy_intervals.extend(arthur_schedule[day])
        if day in michael_schedule:
            busy_intervals.extend(michael_schedule[day])
        
        # If there are no busy intervals, the whole day is free
        if not busy_intervals:
            if work_end - work_start >= meeting_duration:
                start_time = work_start
                end_time = start_time + meeting_duration
                # Format the result
                h1, m1 = divmod(start_time, 60)
                h2, m2 = divmod(end_time, 60)
                time_str = f"{h1:02d}:{m1:02d}:{h2:02d}:{m2:02d}"
                print(day)
                print(time_str)
                return
        
        # Sort busy intervals by start time
        busy_intervals.sort(key=lambda x: x[0])
        
        # Merge overlapping busy intervals
        merged = []
        current_start, current_end = busy_intervals[0]
        for interval in busy_intervals[1:]:
            if interval[0] <= current_end:
                current_end = max(current_end, interval[1])
            else:
                merged.append((current_start, current_end))
                current_start, current_end = interval
        merged.append((current_start, current_end))
        
        # Find free gaps
        gaps = []
        # Gap before first meeting
        if merged[0][0] > work_start:
            gaps.append((work_start, merged[0][0]))
        # Gaps between meetings
        for i in range(1, len(merged)):
            gap_start = merged[i-1][1]
            gap_end = merged[i][0]
            gaps.append((gap_start, gap_end))
        # Gap after last meeting
        if merged[-1][1] < work_end:
            gaps.append((merged[-1][1], work_end))
        
        # Check each gap for sufficient duration
        for gap in gaps:
            gap_start, gap_end = gap
            gap_duration = gap_end - gap_start
            if gap_duration >= meeting_duration:
                start_time = gap_start
                end_time = start_time + meeting_duration
                # Format the result
                h1, m1 = divmod(start_time, 60)
                h2, m2 = divmod(end_time, 60)
                time_str = f"{h1:02d}:{m1:02d}:{h2:02d}:{m2:02d}"
                print(day)
                print(time_str)
                return
    
    # According to the problem, a solution exists, so this line should not be reached
    print("No suitable time found")

if __name__ == "__main__":
    main()