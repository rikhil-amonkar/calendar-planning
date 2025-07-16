def main():
    # Work day: 9:00 to 17:00 (480 minutes from 9:00)
    work_start = 0
    work_end = 480  # 8 hours * 60 minutes
    meeting_duration = 60  # 1 hour in minutes

    # Convert time string to minutes since 9:00
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return (h - 9) * 60 + m

    # Convert minutes since 9:00 back to "HH:MM" format
    def minutes_to_time(minutes):
        total_minutes = 9 * 60 + minutes
        h = total_minutes // 60
        m = total_minutes % 60
        return f"{h:02d}:{m:02d}"

    # Busy intervals for James and John
    james_busy = ["11:30-12:00", "14:30-15:00"]
    john_busy = ["9:30-11:00", "11:30-12:00", "12:30-13:30", "14:30-16:30"]
    
    # Parse and convert busy intervals to minutes
    intervals = []
    for busy_str in james_busy:
        start_str, end_str = busy_str.split('-')
        start_min = time_to_minutes(start_str)
        end_min = time_to_minutes(end_str)
        intervals.append((start_min, end_min))
    
    for busy_str in john_busy:
        start_str, end_str = busy_str.split('-')
        start_min = time_to_minutes(start_str)
        end_min = time_to_minutes(end_str)
        intervals.append((start_min, end_min))
    
    # Sort intervals by start time
    intervals.sort(key=lambda x: x[0])
    
    # Merge overlapping or adjacent intervals
    merged = []
    for start, end in intervals:
        if not merged:
            merged.append([start, end])
        else:
            last = merged[-1]
            if start <= last[1]:
                last[1] = max(last[1], end)
            else:
                merged.append([start, end])
    
    # Find free intervals
    free_intervals = []
    current_start = work_start
    
    for start, end in merged:
        if start > current_start:
            free_intervals.append((current_start, start))
        current_start = max(current_start, end)
    
    if current_start < work_end:
        free_intervals.append((current_start, work_end))
    
    # Find first free interval that can fit the meeting
    meeting_time = None
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            meeting_time = (meeting_start, meeting_end)
            break
    
    # Convert meeting time to string and output
    day = "Monday"
    if meeting_time:
        start_str = minutes_to_time(meeting_time[0])
        end_str = minutes_to_time(meeting_time[1])
        print(day)
        print(f"{start_str}:{end_str}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()