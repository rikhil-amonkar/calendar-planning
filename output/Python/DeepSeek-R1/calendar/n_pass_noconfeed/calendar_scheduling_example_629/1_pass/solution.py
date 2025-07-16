def main():
    # Convert time to minutes for easier calculations
    def time_to_minutes(hour, minute):
        return hour * 60 + minute

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    # Meeting duration in minutes
    meeting_duration = 30

    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    work_start = time_to_minutes(9, 0)
    work_end = time_to_minutes(17, 0)

    # Margaret's availability on Tuesday: only after 14:30 (870 minutes)
    margaret_start = time_to_minutes(14, 30)
    margaret_end = work_end

    # Alexis' blocked times on Tuesday (in minutes)
    alexis_blocks = [
        (time_to_minutes(9, 0), time_to_minutes(9, 30)),
        (time_to_minutes(10, 0), time_to_minutes(10, 30)),
        (time_to_minutes(14, 0), time_to_minutes(16, 30))
    ]

    # Calculate Alexis' free time within Margaret's availability window (870-1020)
    free_start = margaret_start
    free_intervals = []
    for block_start, block_end in alexis_blocks:
        # Only consider blocks that overlap with [margaret_start, margaret_end)
        if block_end > free_start and block_start < margaret_end:
            block_start = max(block_start, free_start)
            block_end = min(block_end, margaret_end)
            if free_start < block_start:
                free_intervals.append((free_start, block_start))
            free_start = block_end
    if free_start < margaret_end:
        free_intervals.append((free_start, margaret_end))

    # Find the first free interval that can accommodate the meeting
    for interval in free_intervals:
        start, end = interval
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            start_str = minutes_to_time(meeting_start)
            end_str = minutes_to_time(meeting_end)
            print("Tuesday")
            print(f"{start_str}:{end_str}")
            return

    # Fallback in case no slot is found (though problem states solution exists)
    print("No suitable time found")

if __name__ == "__main__":
    main()