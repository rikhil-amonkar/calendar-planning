def main():
    # Define work hours in minutes from midnight
    work_start = 9 * 60  # 9:00
    work_end = 17 * 60   # 17:00

    # Nicole's busy intervals in minutes (start, end)
    nicole_busy = [
        (9 * 60, 10 * 60),       # 9:00-10:00
        (10 * 60 + 30, 16 * 60 + 30)  # 10:30-16:30
    ]

    # Generate free intervals for Nicole within work hours
    free_intervals = []
    current = work_start

    for start, end in sorted(nicole_busy):
        if current < start:
            free_intervals.append((current, start))
        current = max(current, end)
    
    if current < work_end:
        free_intervals.append((current, work_end))

    # Filter for intervals that are at least 30 minutes and meet preference (after 16:00)
    meeting_duration = 30
    preferred_intervals = []
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            # Convert start time to minutes for comparison
            if start >= 16 * 60:  # Preference: not before 16:00
                preferred_intervals.append((start, end))

    # Select the first preferred interval
    if preferred_intervals:
        meeting_start, meeting_end = preferred_intervals[0]
        # Adjust meeting end to start + duration
        meeting_end = meeting_start + meeting_duration
    else:
        # Fallback to any available slot (though problem states a solution exists)
        for start, end in free_intervals:
            if end - start >= meeting_duration:
                meeting_start, meeting_end = start, start + meeting_duration
                break

    # Convert minutes to HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        minutes %= 60
        return f"{hours:02d}:{minutes:02d}"

    # Output the meeting day and time range
    print(f"Monday {format_time(meeting_start)}:{format_time(meeting_end)}")

if __name__ == "__main__":
    main()