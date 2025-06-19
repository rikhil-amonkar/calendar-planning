def main():
    # Work hours: 9:00 to 17:00 (480 minutes from 9:00)
    work_start = 0
    work_end = 480
    meeting_duration = 30
    # Juan cannot meet after 16:00 (420 minutes from 9:00), so meeting must end by 420 -> start by 390
    max_start = 390
    
    # Busy intervals in minutes from 9:00
    busy_intervals = [
        # Juan
        (0, 90), (390, 420),
        # Marilyn
        (120, 150), (210, 240),
        # Ronald
        (0, 90), (180, 210), (240, 270), (300, 450)
    ]
    
    # Merge overlapping busy intervals
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
    
    # Find gaps between busy intervals and work boundaries
    gaps = []
    # Before first busy interval
    if merged[0][0] > work_start:
        gaps.append((work_start, merged[0][0]))
    # Between busy intervals
    for i in range(len(merged) - 1):
        gap_start = merged[i][1]
        gap_end = merged[i+1][0]
        if gap_start < gap_end:
            gaps.append((gap_start, gap_end))
    # After last busy interval
    if merged[-1][1] < work_end:
        gaps.append((merged[-1][1], work_end))
    
    # Find the earliest gap that fits the meeting and constraint
    candidate_start = None
    for gap_start, gap_end in gaps:
        # Available start range in this gap
        low = gap_start
        high = min(gap_end - meeting_duration, max_start)
        if low <= high:
            candidate_start = low
            break
    
    # Convert candidate_start to absolute time (from 9:00 base)
    start_minutes = candidate_start
    start_hour = 9 + start_minutes // 60
    start_min = start_minutes % 60
    end_minutes = start_minutes + meeting_duration
    end_hour = 9 + end_minutes // 60
    end_min = end_minutes % 60
    
    # Format as HH:MM:HH:MM
    time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
    
    print("Monday")
    print(time_str)

if __name__ == "__main__":
    main()