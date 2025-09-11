# Define work hours in minutes from 9:00
start_work = 0  # 9:00
end_work = 480   # 17:00
meeting_duration = 30
day = "Monday"

# Busy intervals for each participant in minutes from 9:00
emily = [(60, 90), (420, 450)]
mason = []
maria = [(90, 120), (300, 330)]
carl = [(30, 60), (90, 210), (270, 300), (330, 390), (420, 480)]
david = [(30, 120), (150, 180), (210, 270), (300, 360), (420, 480)]
frank = [(30, 90), (120, 150), (210, 270), (330, 480)]

# Combine all busy intervals
all_busy = emily + mason + maria + carl + david + frank

# If no busy intervals, the entire day is free
if not all_busy:
    # Check if entire day is sufficient
    if end_work - start_work >= meeting_duration:
        gap_start = start_work
        gap_end = end_work
    else:
        gap_start = None
else:
    # Sort busy intervals by start time
    all_busy.sort(key=lambda x: x[0])
    
    # Merge intervals
    merged = []
    current_start, current_end = all_busy[0]
    for i in range(1, len(all_busy)):
        start, end = all_busy[i]
        if start <= current_end:
            current_end = max(current_end, end)
        else:
            merged.append((current_start, current_end))
            current_start, current_end = start, end
    merged.append((current_start, current_end))
    
    # Find free gaps
    gaps = []
    # Check before first busy interval
    if merged[0][0] > start_work:
        gaps.append((start_work, merged[0][0]))
    
    # Check between busy intervals
    for i in range(len(merged) - 1):
        current_end = merged[i][1]
        next_start = merged[i+1][0]
        if next_start > current_end:
            gaps.append((current_end, next_start))
    
    # Check after last busy interval
    if merged[-1][1] < end_work:
        gaps.append((merged[-1][1], end_work))
    
    # Find first gap that meets meeting duration
    gap_start = None
    for gap in gaps:
        start, end = gap
        if end - start >= meeting_duration:
            gap_start = start
            gap_end = end
            break

# If a gap is found, convert to time string
if gap_start is not None:
    # Convert minutes to time string
    def minutes_to_time(minutes):
        total_minutes = 9 * 60 + minutes
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"
    
    start_time_str = minutes_to_time(gap_start)
    end_time_str = minutes_to_time(gap_start + meeting_duration)
    print(f"{day} {start_time_str}:{end_time_str}")
else:
    print("No suitable time found.")