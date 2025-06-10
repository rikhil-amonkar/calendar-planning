def main():
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Work hours: 9:00 to 17:00 -> 0 to 480 minutes (from 9:00)
    # But Albert cannot meet after 11:00 -> meeting must end by 11:00 (120 minutes from 9:00)
    meeting_end_max = 120  # 11:00 is 120 minutes after 9:00
    
    # Albert's busy times in minutes from 9:00
    albert_busy = [
        (0, 60),    # 9:00 to 10:00
        (90, 180),   # 10:30 to 12:00 -> but we'll clamp to 120 for meeting_end_max
        (360, 450)   # 15:00 to 16:30 -> irrelevant for meeting before 11:00
    ]
    
    # Collect busy intervals that are within [0, meeting_end_max]
    relevant_busy = []
    for s, e in albert_busy:
        if s >= meeting_end_max:
            continue
        end_clamped = min(e, meeting_end_max)
        if end_clamped > s:  # Only add if the interval is non-empty
            relevant_busy.append((s, end_clamped))
    
    # Sort the intervals by start time
    relevant_busy.sort(key=lambda x: x[0])
    
    # Merge overlapping intervals (though in this case, they are disjoint)
    merged_busy = []
    if relevant_busy:
        current_start, current_end = relevant_busy[0]
        for i in range(1, len(relevant_busy)):
            s, e = relevant_busy[i]
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged_busy.append((current_start, current_end))
                current_start, current_end = s, e
        merged_busy.append((current_start, current_end))
    else:
        merged_busy = []
    
    # Find free intervals in [0, meeting_end_max]
    free_intervals = []
    current = 0
    for start_busy, end_busy in merged_busy:
        if current < start_busy:
            free_intervals.append((current, start_busy))
        current = max(current, end_busy)
    if current < meeting_end_max:
        free_intervals.append((current, meeting_end_max))
    
    # Find the first free interval that is at least meeting_duration long
    meeting_start_min = None
    for start_free, end_free in free_intervals:
        if end_free - start_free >= meeting_duration:
            meeting_start_min = start_free
            break
    
    if meeting_start_min is None:
        print("No solution found")
        return
    
    # Convert meeting_start_min to time string
    total_minutes = meeting_start_min
    hours = total_minutes // 60
    minutes = total_minutes % 60
    start_time = f"{9 + hours}:{minutes:02d}"
    
    # Calculate and convert end time
    end_minutes = meeting_start_min + meeting_duration
    end_hours = end_minutes // 60
    end_minutes_rem = end_minutes % 60
    end_time = f"{9 + end_hours}:{end_minutes_rem:02d}"
    
    print(f"Monday, {start_time}, {end_time}")

if __name__ == "__main__":
    main()