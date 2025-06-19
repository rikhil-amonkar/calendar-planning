def main():
    work_start = 0   # 9:00 in minutes from 9:00
    work_end = 480   # 17:00
    meeting_duration = 30
    max_start = 390  # 15:30 (meeting must end by 16:00)
    
    days_schedule = [
        ('Monday', [
            (0, 90), (390, 420),   # Juan
            (120, 150), (210, 240), # Marilyn
            (0, 90), (180, 210), (240, 270), (300, 450) # Ronald
        ]),
        ('Tuesday', []),
        ('Wednesday', []),
        ('Thursday', []),
        ('Friday', [])
    ]
    
    candidate_day = None
    candidate_start = None
    
    for day, busy_intervals in days_schedule:
        if not busy_intervals:
            # Entire workday free - use earliest possible time
            candidate_start = work_start
            candidate_day = day
            break
        
        # Merge overlapping intervals
        busy_intervals.sort()
        merged = []
        start, end = busy_intervals[0]
        for s, e in busy_intervals[1:]:
            if s <= end:
                end = max(end, e)
            else:
                merged.append((start, end))
                start, end = s, e
        merged.append((start, end))
        
        # Find free gaps
        gaps = []
        if merged[0][0] > work_start:
            gaps.append((work_start, merged[0][0]))
        for i in range(len(merged)-1):
            gap_start = merged[i][1]
            gap_end = merged[i+1][0]
            if gap_start < gap_end:
                gaps.append((gap_start, gap_end))
        if merged[-1][1] < work_end:
            gaps.append((merged[-1][1], work_end))
        
        # Check gaps for valid meeting time
        for gap_start, gap_end in gaps:
            low = gap_start
            high = min(gap_end - meeting_duration, max_start)
            if low <= high:
                candidate_start = low
                candidate_day = day
                break
        if candidate_start is not None:
            break
    
    # Convert to time string with correct formatting
    total_minutes_start = candidate_start
    start_hour = 9 + total_minutes_start // 60
    start_min = total_minutes_start % 60
    total_minutes_end = candidate_start + meeting_duration
    end_hour = 9 + total_minutes_end // 60
    end_min = total_minutes_end % 60
    
    # Format time as "HH:MM-HH:MM" without zero-padding hours
    start_str = f"{start_hour}:{start_min:02d}"
    end_str = f"{end_hour}:{end_min:02d}"
    time_str = f"{start_str}-{end_str}"
    
    print(candidate_day)
    print(time_str)

if __name__ == "__main__":
    main()