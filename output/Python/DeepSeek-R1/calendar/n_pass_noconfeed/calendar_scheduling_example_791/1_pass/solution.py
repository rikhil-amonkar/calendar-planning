def main():
    # Convert time to minutes for easier calculation
    work_start = 9 * 60  # 9:00
    work_end = 17 * 60   # 17:00
    meeting_duration = 30  # minutes
    deadline = 13 * 60 + 30  # 13:30 in minutes

    # Wednesday busy intervals in minutes (start, end)
    busy_nicole = [
        (10 * 60, 11 * 60),          # 10:00-11:00
        (12 * 60 + 30, 15 * 60),     # 12:30-15:00
        (16 * 60, 17 * 60)           # 16:00-17:00
    ]
    busy_ruth = [
        (9 * 60, 10 * 60 + 30),      # 9:00-10:30
        (11 * 60, 11 * 60 + 30),     # 11:00-11:30
        (12 * 60, 12 * 60 + 30),     # 12:00-12:30
        (13 * 60 + 30, 15 * 60 + 30),# 13:30-15:30
        (16 * 60, 16 * 60 + 30)      # 16:00-16:30
    ]

    # Generate free intervals for Nicole
    free_nicole = []
    current = work_start
    for start, end in sorted(busy_nicole, key=lambda x: x[0]):
        if current < start:
            free_nicole.append((current, start))
        current = end
    if current < work_end:
        free_nicole.append((current, work_end))

    # Generate free intervals for Ruth
    free_ruth = []
    current = work_start
    for start, end in sorted(busy_ruth, key=lambda x: x[0]):
        if current < start:
            free_ruth.append((current, start))
        current = end
    if current < work_end:
        free_ruth.append((current, work_end))

    # Find first overlapping free slot of at least 30 minutes that ends by deadline
    meeting_start = None
    day = "Wednesday"
    for nic_start, nic_end in free_nicole:
        for ruth_start, ruth_end in free_ruth:
            # Calculate overlap
            overlap_start = max(nic_start, ruth_start)
            overlap_end = min(nic_end, ruth_end)
            if overlap_start >= overlap_end:
                continue
            # Available end is min(overlap_end, deadline) to enforce deadline
            available_end = min(overlap_end, deadline)
            # Check if a 30-minute slot exists within the overlap ending by deadline
            if overlap_start + meeting_duration <= available_end:
                meeting_start = overlap_start
                break
        if meeting_start is not None:
            break

    # Convert meeting start and end to HH:MM format
    start_hour = meeting_start // 60
    start_minute = meeting_start % 60
    end_meeting = meeting_start + meeting_duration
    end_hour = end_meeting // 60
    end_minute = end_meeting % 60

    # Format as HH:MM:HH:MM
    time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"

    # Output day and time string
    print(day)
    print(time_str)

if __name__ == "__main__":
    main()