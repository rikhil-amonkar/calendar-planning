def main():
    # Convert time to minutes from midnight
    work_start = 9 * 60  # 9:00
    work_end = 17 * 60   # 17:00
    meeting_duration = 30  # minutes

    # Deborah: free entire day within work hours
    deborah_free = [(work_start, work_end)]
    
    # Albert's constraints and busy intervals
    albert_busy = [
        (9 * 60, 10 * 60),     # 9:00-10:00
        (10 * 60 + 30, 12 * 60) # 10:30-12:00
    ]
    # Albert cannot meet after 11:00, so his available window is [9:00, 11:00]
    albert_window = (9 * 60, 11 * 60)  # 540 to 660 minutes
    
    # Start with Albert's available window as the initial free interval
    albert_free = [albert_window]
    
    # Subtract each busy interval from Albert's free intervals
    for busy in albert_busy:
        new_free = []
        for free in albert_free:
            # Check if busy interval overlaps with free interval
            if busy[1] <= free[0] or busy[0] >= free[1]:
                # No overlap, keep the free interval
                new_free.append(free)
            else:
                # Overlap exists; split the free interval around the busy interval
                if free[0] < busy[0]:
                    new_free.append((free[0], busy[0]))
                if free[1] > busy[1]:
                    new_free.append((busy[1], free[1]))
        albert_free = new_free
    
    # Find common free time between Deborah and Albert
    common_free = []
    for d_interval in deborah_free:
        for a_interval in albert_free:
            start = max(d_interval[0], a_interval[0])
            end = min(d_interval[1], a_interval[1])
            if start < end:
                common_free.append((start, end))
    
    # Find the first common free interval that fits the meeting duration
    for interval in common_free:
        if interval[1] - interval[0] >= meeting_duration:
            start_time = interval[0]
            end_time = start_time + meeting_duration
            # Convert minutes to HH:MM format
            start_hour = start_time // 60
            start_minute = start_time % 60
            end_hour = end_time // 60
            end_minute = end_time % 60
            time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
            print("Monday", time_str, sep=", ")
            return
    
    # If no suitable time is found, print an error
    print("No suitable time found.")

if __name__ == "__main__":
    main()