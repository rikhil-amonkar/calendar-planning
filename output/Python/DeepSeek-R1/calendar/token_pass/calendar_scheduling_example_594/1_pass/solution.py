def main():
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Work hours: 9:00 to 17:00 (in minutes from 0:00)
    work_start = 9 * 60
    work_end = 17 * 60
    
    # Busy intervals for Adam and Roy in minutes from 0:00
    adam_busy = [
        (9 * 60 + 30, 10 * 60),
        (12 * 60 + 30, 13 * 60),
        (14 * 60 + 30, 15 * 60),
        (16 * 60 + 30, 17 * 60)
    ]
    
    roy_busy = [
        (10 * 60, 11 * 60),
        (11 * 60 + 30, 13 * 60),
        (13 * 60 + 30, 14 * 60 + 30),
        (16 * 60 + 30, 17 * 60)
    ]
    
    # Combine and sort all busy intervals
    all_busy = adam_busy + roy_busy
    all_busy.sort(key=lambda x: x[0])
    
    # Merge overlapping busy intervals
    merged_busy = []
    for start, end in all_busy:
        if not merged_busy:
            merged_busy.append([start, end])
        else:
            last = merged_busy[-1]
            if start <= last[1]:
                last[1] = max(last[1], end)
            else:
                merged_busy.append([start, end])
    
    # Find free intervals within work hours
    free_intervals = []
    current = work_start
    
    for busy_start, busy_end in merged_busy:
        if busy_start > current:
            free_intervals.append((current, busy_start))
        current = max(current, busy_end)
    
    if current < work_end:
        free_intervals.append((current, work_end))
    
    # Find the first free interval that can accommodate the meeting
    for start, end in free_intervals:
        duration = end - start
        if duration >= meeting_duration:
            meeting_start = start
            meeting_end = meeting_start + meeting_duration
            break
    
    # Convert minutes to HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    start_str = format_time(meeting_start)
    end_str = format_time(meeting_end)
    
    # Output the result
    print(f"Monday {start_str}:{end_str}")

if __name__ == "__main__":
    main()