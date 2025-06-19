def main():
    # Convert time to minutes since midnight for easier calculations
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes

    # Convert minutes back to HH:MM format
    def minutes_to_time(total_minutes):
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    # Work hours and constraints
    day_start = time_to_minutes("09:00")
    day_end = time_to_minutes("13:30")  # Meeting must end by 13:30 (Ruth's constraint)

    # Nicole's busy intervals on Wednesday (converted to minutes, truncated to day_end)
    nicole_busy = [
        (time_to_minutes("10:00"), min(time_to_minutes("11:00"), day_end)),
        (time_to_minutes("12:30"), min(time_to_minutes("15:00"), day_end))
    ]

    # Ruth's busy intervals on Wednesday (converted to minutes)
    ruth_busy = [
        (time_to_minutes("09:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30"))
    ]

    # Combine and sort all busy intervals
    all_busy = nicole_busy + ruth_busy
    all_busy.sort(key=lambda x: x[0])

    # Merge overlapping or adjacent intervals
    merged = []
    if all_busy:
        current_start, current_end = all_busy[0]
        for s, e in all_busy[1:]:
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))

    # Find free intervals within the day
    free_intervals = []
    current = day_start
    for start, end in merged:
        if start > current:
            free_intervals.append((current, start))
        current = end
    if current < day_end:
        free_intervals.append((current, day_end))

    # Check each free interval for a 30-minute slot
    meeting_duration = 30
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            # Format the meeting time as HH:MM:HH:MM
            start_str = minutes_to_time(meeting_start)
            end_str = minutes_to_time(meeting_end)
            print("Wednesday")
            print(f"{start_str}:{end_str}")
            return

    # If no slot found (though problem states there is a solution)
    print("No suitable time found")

if __name__ == "__main__":
    main()