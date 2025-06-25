def main():
    # Work hours: 9:00 to 17:00 (converted to minutes since 9:00: 0 to 480 minutes)
    work_start = 0
    work_end = 480  # 8 hours * 60 minutes

    # Helper function to convert time string to minutes since 9:00
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return (hour - 9) * 60 + minute

    # Parse Danielle's meetings
    danielle_meetings = [
        ("9:00", "10:00"),
        ("10:30", "11:00"),
        ("14:30", "15:00"),
        ("15:30", "16:00"),
        ("16:30", "17:00")
    ]
    danielle_busy = []
    for start, end in danielle_meetings:
        s = time_to_minutes(start)
        e = time_to_minutes(end)
        danielle_busy.append((s, e))

    # Parse Bruce's meetings
    bruce_meetings = [
        ("11:00", "11:30"),
        ("12:30", "13:00"),
        ("14:00", "14:30"),
        ("15:30", "16:00")
    ]
    bruce_busy = []
    for start, end in bruce_meetings:
        s = time_to_minutes(start)
        e = time_to_minutes(end)
        bruce_busy.append((s, e))

    # Parse Eric's meetings
    eric_meetings = [
        ("9:00", "9:30"),
        ("10:00", "11:00"),
        ("11:30", "13:00"),
        ("14:30", "15:30")
    ]
    eric_busy = []
    for start, end in eric_meetings:
        s = time_to_minutes(start)
        e = time_to_minutes(end)
        eric_busy.append((s, e))

    # Combine all busy intervals
    all_busy = danielle_busy + bruce_busy + eric_busy
    
    # Sort by start time
    all_busy.sort(key=lambda x: x[0])
    
    # Merge overlapping or adjacent intervals
    merged_busy = []
    current_start, current_end = all_busy[0]
    for i in range(1, len(all_busy)):
        s, e = all_busy[i]
        if s <= current_end:
            current_end = max(current_end, e)
        else:
            merged_busy.append((current_start, current_end))
            current_start, current_end = s, e
    merged_busy.append((current_start, current_end))
    
    # Find free intervals
    free_intervals = []
    # Before first meeting
    if merged_busy[0][0] > work_start:
        free_intervals.append((work_start, merged_busy[0][0]))
    
    # Between meetings
    for i in range(len(merged_busy) - 1):
        end_current = merged_busy[i][1]
        start_next = merged_busy[i+1][0]
        if end_current < start_next:
            free_intervals.append((end_current, start_next))
    
    # After last meeting
    if merged_busy[-1][1] < work_end:
        free_intervals.append((merged_busy[-1][1], work_end))
    
    # Find first free interval that is at least 60 minutes
    meeting_duration = 60
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            break
    
    # Convert meeting start and end back to time strings
    def minutes_to_time(minutes):
        total_minutes = minutes
        hour = 9 + total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    
    # Output day and time range in the format HH:MM:HH:MM
    print("Monday")
    print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()