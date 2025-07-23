def main():
    # Convert time string to minutes since midnight
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        return int(parts[0]) * 60 + int(parts[1])

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    # Define work hours and meeting duration
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 60  # minutes

    # Define busy intervals in minutes (start, end)
    james_busy = [
        ("11:30", "12:00"),
        ("14:30", "15:00")
    ]
    john_busy = [
        ("09:30", "11:00"),
        ("11:30", "12:00"),
        ("12:30", "13:30"),
        ("14:30", "16:30")
    ]

    # Combine and convert all busy intervals to minutes
    busy_intervals = []
    for start, end in james_busy:
        busy_intervals.append((time_to_minutes(start), time_to_minutes(end)))
    for start, end in john_busy:
        busy_intervals.append((time_to_minutes(start), time_to_minutes(end)))

    # Sort intervals by start time
    busy_intervals.sort(key=lambda x: x[0])

    # Merge overlapping intervals
    merged = []
    if busy_intervals:
        merged = [busy_intervals[0]]
        for i in range(1, len(busy_intervals)):
            current_start, current_end = busy_intervals[i]
            last_start, last_end = merged[-1]
            if current_start <= last_end:
                merged[-1] = (last_start, max(last_end, current_end))
            else:
                merged.append((current_start, current_end))

    # Find free intervals within work hours
    free_intervals = []
    current = work_start

    for start, end in merged:
        if current < start:
            free_intervals.append((current, start))
        current = max(current, end)
    
    if current < work_end:
        free_intervals.append((current, work_end))

    # Find the first free interval that can fit the meeting
    meeting_interval = None
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            meeting_interval = (meeting_start, meeting_end)
            break

    # Format the meeting time and day
    if meeting_interval:
        start_str = minutes_to_time(meeting_interval[0])
        end_str = minutes_to_time(meeting_interval[1])
        print(f"{start_str}:{end_str}")
        print("Monday")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()