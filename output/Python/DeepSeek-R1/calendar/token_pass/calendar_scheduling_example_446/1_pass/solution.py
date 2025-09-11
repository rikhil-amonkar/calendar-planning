def main():
    # Define the work hours: 9:00 to 17:00 in minutes from 9:00
    work_start = 0    # 9:00
    work_end = 480    # 17:00
    meeting_duration = 30

    # Busy intervals for each participant in minutes from 9:00
    busy_intervals = [
        # Megan
        (0, 30), (60, 120), (180, 210),
        # Christine
        (0, 30), (150, 180), (240, 300), (390, 450),
        # Sara
        (150, 180), (330, 360),
        # Bruce
        (30, 60), (90, 180), (210, 300), (330, 360), (390, 450),
        # Kathryn
        (60, 390), (420, 450),
        # Billy
        (0, 30), (120, 150), (180, 300), (330, 390)
    ]

    # Sort busy intervals by start time
    busy_intervals.sort(key=lambda x: x[0])

    # Merge overlapping intervals
    merged_busy = []
    current_start, current_end = busy_intervals[0]
    for interval in busy_intervals[1:]:
        if interval[0] <= current_end:
            current_end = max(current_end, interval[1])
        else:
            merged_busy.append((current_start, current_end))
            current_start, current_end = interval
    merged_busy.append((current_start, current_end))

    # Find free intervals within work hours
    free_intervals = []
    previous_end = work_start
    for busy in merged_busy:
        if busy[0] > previous_end:
            free_intervals.append((previous_end, busy[0]))
        previous_end = max(previous_end, busy[1])
    if previous_end < work_end:
        free_intervals.append((previous_end, work_end))

    # Find a free interval that can accommodate the meeting
    for free in free_intervals:
        start, end = free
        if end - start >= meeting_duration:
            # Convert start and end to HH:MM format
            start_time = start
            start_hour = 9 + start_time // 60
            start_minute = start_time % 60
            end_time = start + meeting_duration
            end_hour = 9 + end_time // 60
            end_minute = end_time % 60
            # Format the time string
            time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
            print("Monday", time_str)
            return

    # If no slot found, but problem states there is a solution
    print("No suitable time found")

if __name__ == "__main__":
    main()