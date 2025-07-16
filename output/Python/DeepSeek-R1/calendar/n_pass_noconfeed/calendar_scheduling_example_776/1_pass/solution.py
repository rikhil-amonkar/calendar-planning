def main():
    # Define work hours in minutes (9:00 AM to 5:00 PM)
    work_start = 540   # 9:00 in minutes
    work_end = 1020    # 17:00 in minutes

    # Jennifer's busy intervals in minutes (start inclusive, end exclusive)
    jennifer_busy = {
        'Monday': [(540, 660), (690, 780), (810, 870), (900, 1020)],
        'Tuesday': [(540, 690), (720, 1020)],
        'Wednesday': [(540, 690), (720, 750), (780, 840), (870, 960), (990, 1020)]
    }
    
    # Days to consider in order
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Monday constraint: meeting must end by 14:30 (870 minutes)
    monday_constraint = 870
    
    found = False
    result_day = None
    meeting_start_minutes = None
    meeting_end_minutes = None

    for day in days:
        busy_intervals = jennifer_busy[day]
        # Sort intervals by start time
        busy_intervals_sorted = sorted(busy_intervals, key=lambda x: x[0])
        
        # Compute free gaps
        current = work_start
        gaps = []
        for interval in busy_intervals_sorted:
            start_interval, end_interval = interval
            if current < start_interval:
                gaps.append((current, start_interval))
            current = max(current, end_interval)
        if current < work_end:
            gaps.append((current, work_end))
            
        # Check each gap for availability
        for gap in gaps:
            start_gap, end_gap = gap
            gap_duration = end_gap - start_gap
            if gap_duration >= meeting_duration:
                candidate_start = start_gap
                candidate_end = candidate_start + meeting_duration
                # Skip if on Monday and violates the end constraint
                if day == 'Monday' and candidate_end > monday_constraint:
                    continue
                # Valid candidate found
                result_day = day
                meeting_start_minutes = candidate_start
                meeting_end_minutes = candidate_end
                found = True
                break  # Break inner loop
        if found:
            break  # Break outer loop

    # Format and output result
    if found:
        # Convert minutes to HH:MM components
        start_hour = meeting_start_minutes // 60
        start_minute = meeting_start_minutes % 60
        end_hour = meeting_end_minutes // 60
        end_minute = meeting_end_minutes % 60
        
        # Format as two-digit strings
        time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print(result_day)
        print("{" + time_str + "}")
    else:
        # Fallback (though problem states a solution exists)
        print("No valid time found")

if __name__ == "__main__":
    main()