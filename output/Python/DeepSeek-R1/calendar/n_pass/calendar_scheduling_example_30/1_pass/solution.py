def main():
    # Work hours: 9:00 to 17:00 (480 minutes from 9:00)
    work_start = 0
    work_end = 480
    meeting_duration = 30
    
    # Busy intervals in minutes from 9:00
    jeffrey_busy = [(30, 60), (90, 120)]
    virginia_busy = [(0, 30), (60, 90), (330, 360), (420, 450)]
    melissa_busy = [(0, 150), (180, 210), (240, 360), (420, 480)]
    
    # Combine all busy intervals
    all_busy = jeffrey_busy + virginia_busy + melissa_busy
    all_busy.sort(key=lambda x: x[0])
    
    # Merge overlapping intervals
    merged = []
    for start, end in all_busy:
        if not merged:
            merged.append([start, end])
        else:
            last = merged[-1]
            if start <= last[1]:
                last[1] = max(last[1], end)
            else:
                merged.append([start, end])
    
    # Find free intervals within work hours
    free_intervals = []
    current = work_start
    for interval in merged:
        if current < interval[0]:
            gap_start = current
            gap_end = interval[0]
            gap_duration = gap_end - gap_start
            if gap_duration >= meeting_duration:
                free_intervals.append((gap_start, gap_end))
        current = max(current, interval[1])
    if current < work_end:
        gap_start = current
        gap_end = work_end
        gap_duration = gap_end - gap_start
        if gap_duration >= meeting_duration:
            free_intervals.append((gap_start, gap_end))
    
    # Find a meeting slot (30 minutes) that ends by 14:00 (300 minutes) if possible
    candidate = None
    for start, end in free_intervals:
        meeting_end = start + meeting_duration
        if meeting_end <= end and meeting_end <= 300:  # 300 minutes is 14:00
            candidate = (start, meeting_end)
            break
    
    # If no slot ending by 14:00, take the first available slot
    if candidate is None:
        for start, end in free_intervals:
            if start + meeting_duration <= end:
                candidate = (start, start + meeting_duration)
                break
    
    # Convert minutes to time string (HH:MM)
    def format_time(minutes):
        total_minutes = minutes
        hours = 9 + total_minutes // 60
        minutes_part = total_minutes % 60
        return f"{hours:02d}:{minutes_part:02d}"
    
    start_time_str = format_time(candidate[0])
    end_time_str = format_time(candidate[1])
    time_range_str = f"{start_time_str}:{end_time_str}"
    
    # Output day and time range
    print("Monday")
    print(time_range_str)

if __name__ == "__main__":
    main()