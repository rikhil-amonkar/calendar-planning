def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    total_minutes_since_midnight = hours * 60 + minutes
    return total_minutes_since_midnight - 540  # 540 = 9*60 (minutes from midnight to 9:00)

def minutes_to_time(m):
    total_minutes_since_midnight = 540 + m
    hours = total_minutes_since_midnight // 60
    minutes = total_minutes_since_midnight % 60
    return f"{hours}:{minutes:02d}"

# Define busy times for Bryan and Nicholas
bryan_busy = {
    'Thursday': [('9:30', '10:00'), ('12:30', '13:00')],
    'Friday': [('10:30', '11:00'), ('14:00', '14:30')]
}

nicholas_busy = {
    'Monday': [('11:30', '12:00'), ('13:00', '15:30')],
    'Tuesday': [('9:00', '9:30'), ('11:00', '13:30'), ('14:00', '16:30')],
    'Wednesday': [('9:00', '9:30'), ('10:00', '11:00'), ('11:30', '13:30'), ('14:00', '14:30'), ('15:00', '16:30')],
    'Thursday': [('10:30', '11:30'), ('12:00', '12:30'), ('15:00', '15:30'), ('16:30', '17:00')],
    'Friday': [('9:00', '10:30'), ('11:00', '12:00'), ('12:30', '14:30'), ('15:30', '16:00'), ('16:30', '17:00')]
}

# Preferred order of days to try: Wednesday, Friday, Tuesday, Monday, Thursday
days_to_try = ['Wednesday', 'Friday', 'Tuesday', 'Monday', 'Thursday']
meeting_duration = 60  # 60 minutes

for day in days_to_try:
    busy_intervals = []
    
    # Add Bryan's meetings for the day
    if day in bryan_busy:
        for interval in bryan_busy[day]:
            start_min = time_to_minutes(interval[0])
            end_min = time_to_minutes(interval[1])
            busy_intervals.append((start_min, end_min))
    
    # Add Nicholas's meetings for the day
    if day in nicholas_busy:
        for interval in nicholas_busy[day]:
            start_min = time_to_minutes(interval[0])
            end_min = time_to_minutes(interval[1])
            busy_intervals.append((start_min, end_min))
    
    # If no meetings, the whole day is free
    if not busy_intervals:
        start_time = minutes_to_time(0)
        end_time = minutes_to_time(60)
        print(day)
        print(f"{start_time}:{end_time}")
        break
    
    # Sort intervals by start time
    busy_intervals.sort(key=lambda x: x[0])
    
    # Merge overlapping intervals
    merged = []
    current_start, current_end = busy_intervals[0]
    for i in range(1, len(busy_intervals)):
        s, e = busy_intervals[i]
        if s <= current_end:
            current_end = max(current_end, e)
        else:
            merged.append((current_start, current_end))
            current_start, current_end = s, e
    merged.append((current_start, current_end))
    
    # Check for gaps: from start of day (0) to first meeting, between meetings, and from last meeting to end (480 minutes)
    gaps = []
    # Gap before first meeting
    first_start = merged[0][0]
    if first_start > 0:
        gaps.append((0, first_start))
    
    # Gaps between meetings
    for i in range(len(merged) - 1):
        current_end = merged[i][1]
        next_start = merged[i+1][0]
        if next_start > current_end:
            gaps.append((current_end, next_start))
    
    # Gap after last meeting
    last_end = merged[-1][1]
    if last_end < 480:
        gaps.append((last_end, 480))
    
    # Find the first gap that can fit the meeting
    found = False
    for gap in gaps:
        gap_start, gap_end = gap
        if gap_end - gap_start >= meeting_duration:
            meeting_start = gap_start
            meeting_end = meeting_start + meeting_duration
            start_time_str = minutes_to_time(meeting_start)
            end_time_str = minutes_to_time(meeting_end)
            print(day)
            print(f"{start_time_str}:{end_time_str}")
            found = True
            break
    
    if found:
        break