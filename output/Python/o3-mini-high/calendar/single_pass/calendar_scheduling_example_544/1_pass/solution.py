def minutes_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    # Constants in minutes
    WORK_START = 9 * 60        # 09:00
    WORK_END = 17 * 60         # 17:00
    MUST_END_BY = 11 * 60      # Albert cannot meet after 11:00
    MEETING_DURATION = 30      # 30 minutes meeting

    # Albert's busy intervals (in minutes)
    busy_intervals = [
        (9 * 60, 10 * 60),            # 09:00 to 10:00
        (10 * 60 + 30, 12 * 60),       # 10:30 to 12:00
        (15 * 60, 16 * 60 + 30)        # 15:00 to 16:30
    ]

    # Deborah is free all day, so we only need to check Albert's availability.

    # Calculate Albert's free intervals during his workday
    free_intervals = []
    current = WORK_START
    for start, end in busy_intervals:
        if start > current:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < WORK_END:
        free_intervals.append((current, WORK_END))

    # Apply the constraint that the meeting must end by 11:00 (MUST_END_BY)
    available_slot = None
    for free_start, free_end in free_intervals:
        # Adjust free interval with the constraint that no meeting goes past 11:00
        interval_start = max(free_start, WORK_START)
        interval_end = min(free_end, MUST_END_BY)
        if interval_end - interval_start >= MEETING_DURATION:
            available_slot = (interval_start, interval_start + MEETING_DURATION)
            break

    if available_slot:
        start_time = minutes_to_str(available_slot[0])
        end_time = minutes_to_str(available_slot[1])
        # Output format: Day HH:MM:HH:MM
        print(f"Monday {start_time}:{end_time}")
    else:
        print("No available time slot meets all constraints.")

if __name__ == "__main__":
    main()