def main():
    # Define constants
    work_start = 9 * 60  # 9:00 AM in minutes
    work_end_albert = 11 * 60  # Albert can't meet after 11:00 AM
    meeting_duration = 30  # minutes

    # Albert's original blocked times (in minutes since midnight)
    albert_blocked = [
        (9 * 60, 10 * 60),  # 9:00-10:00
        (10 * 60 + 30, 12 * 60),  # 10:30-12:00
        (15 * 60, 16 * 60 + 30),  # 15:00-16:30
    ]

    # Adjust blocked intervals to not exceed Albert's latest possible time
    adjusted_blocked = []
    for start, end in albert_blocked:
        if start >= work_end_albert:
            continue  # Skip if starts after Albert's cutoff
        new_start = start
        new_end = min(end, work_end_albert)
        adjusted_blocked.append((new_start, new_end))

    # Sort adjusted blocked intervals by start time
    adjusted_blocked.sort()

    # Find available time slots
    available_slots = []
    prev_end = work_start

    for start, end in adjusted_blocked:
        available_start = prev_end
        available_end = start
        if available_end - available_start >= meeting_duration:
            available_slots.append((available_start, available_end))
        prev_end = end

    # Check the time after the last blocked interval
    available_start = prev_end
    available_end = work_end_albert
    if available_end - available_start >= meeting_duration:
        available_slots.append((available_start, available_end))

    # Find the earliest available slot
    if available_slots:
        earliest_start, earliest_end = available_slots[0]
        # Convert to HH:MM format
        start_hh = earliest_start // 60
        start_mm = earliest_start % 60
        end_hh = earliest_end // 60
        end_mm = earliest_end % 60
        start_time = f"{start_hh:02d}:{start_mm:02d}"
        end_time = f"{end_hh:02d}:{end_mm:02d}"
        day = "Monday"
        print(f"{start_time}:{end_time} {day}")
    else:
        # According to the problem, there's a solution, so this shouldn't happen
        pass

if __name__ == "__main__":
    main()