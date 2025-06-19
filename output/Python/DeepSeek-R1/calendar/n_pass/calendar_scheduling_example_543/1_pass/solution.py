def main():
    # Work hours: 9:00 to 17:00 (converted to minutes from 9:00)
    work_start = 0      # 9:00
    work_end = 8 * 60   # 17:00 is 8 hours after 9:00 -> 480 minutes

    # Helper function to convert time string to minutes from 9:00
    def time_str_to_minutes(time_str):
        parts = time_str.split(':')
        hours = int(parts[0])
        minutes = int(parts[1])
        return (hours - 9) * 60 + minutes

    # Helper function to convert minutes back to time string (HH:MM format with two digits for hour and minute)
    def minutes_to_time_str(minutes_val):
        total_minutes = minutes_val
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    # James' busy intervals in string format (start, end)
    james_busy_str = [
        ("11:30", "12:00"),
        ("14:30", "15:00")
    ]
    # Convert to minutes
    james_busy = []
    for start, end in james_busy_str:
        s_min = time_str_to_minutes(start)
        e_min = time_str_to_minutes(end)
        james_busy.append((s_min, e_min))

    # John's busy intervals in string format
    john_busy_str = [
        ("9:30", "11:00"),
        ("11:30", "12:00"),
        ("12:30", "13:30"),
        ("14:30", "16:30")
    ]
    # Convert to minutes
    john_busy = []
    for start, end in john_busy_str:
        s_min = time_str_to_minutes(start)
        e_min = time_str_to_minutes(end)
        john_busy.append((s_min, e_min))

    # Function to compute free intervals given busy intervals and work hours
    def get_free_intervals(busy_intervals, start_bound, end_bound):
        if not busy_intervals:
            return [(start_bound, end_bound)]
        # Sort by start time
        sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
        free = []
        current = start_bound
        for start, end in sorted_busy:
            if current < start:
                free.append((current, start))
            current = max(current, end)
        if current < end_bound:
            free.append((current, end_bound))
        return free

    # Get free intervals for James and John
    james_free = get_free_intervals(james_busy, work_start, work_end)
    john_free = get_free_intervals(john_busy, work_start, work_end)

    # Find common free intervals (intersection of both free intervals)
    common_free = []
    for j_interval in james_free:
        for o_interval in john_free:
            low = max(j_interval[0], o_interval[0])
            high = min(j_interval[1], o_interval[1])
            if low < high:
                common_free.append((low, high))

    # Duration of meeting in minutes
    meeting_duration = 60

    # Find the first common free interval that can fit the meeting
    meeting_start = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_start = start
            break

    if meeting_start is None:
        # According to the problem, there is a solution, so this should not happen
        print("No suitable time found")
        return

    meeting_end = meeting_start + meeting_duration

    # Convert to time strings
    start_time_str = minutes_to_time_str(meeting_start)
    end_time_str = minutes_to_time_str(meeting_end)

    # Format the time range as HH:MM:HH:MM
    time_range_str = f"{start_time_str}:{end_time_str}"

    # Output the day and time range
    print(f"Monday {time_range_str}")

if __name__ == "__main__":
    main()