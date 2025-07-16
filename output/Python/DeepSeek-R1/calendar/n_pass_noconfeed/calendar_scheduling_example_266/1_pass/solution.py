def main():
    # Convert time to minutes function
    def time_to_minutes(time_str):
        parts = list(map(int, time_str.split(':')))
        return parts[0] * 60 + parts[1]
    
    # Convert minutes to time string (HH:MM)
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    # Work hours (9:00 to 17:00) in minutes
    work_start = 9 * 60   # 540 minutes
    work_end = 17 * 60    # 1020 minutes
    
    # Busy intervals for all participants (start and end in minutes)
    busy_intervals = [
        # Joe's meetings
        (time_to_minutes("9:30"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        # Keith's blocked times
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("15:00"), time_to_minutes("15:30")),
        # Patricia's blocked times
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        # Nancy's blocked times
        (time_to_minutes("9:00"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("16:30")),
        # Pamela's blocked times
        (time_to_minutes("9:00"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    
    # Create events: (time, delta) where +1 for busy start, -1 for busy end
    events = []
    for start, end in busy_intervals:
        events.append((start, 1))
        events.append((end, -1))
    
    # Sort events by time, and for same time: process ends (-1) before starts (1)
    events.sort(key=lambda x: (x[0], x[1]))
    
    # Find free intervals by scanning events
    free_intervals = []
    counter = 0
    free_start = work_start  # current free period starts at work_start
    
    for time, delta in events:
        if counter == 0:  # currently free
            # If time is after current free_start, record free interval [free_start, time]
            if time > free_start:
                free_intervals.append((free_start, time))
        counter += delta
        if counter == 0:  # just became free
            free_start = time  # next free period starts at this end time
    
    # After processing events, check if there's free time until work_end
    if counter == 0 and free_start < work_end:
        free_intervals.append((free_start, work_end))
    
    # Find the first free interval with at least 30 minutes
    meeting_start = None
    for start, end in free_intervals:
        if end - start >= 30:
            meeting_start = start
            meeting_end = meeting_start + 30
            break
    
    # Convert meeting times to HH:MM format and output
    if meeting_start is not None:
        start_hour = meeting_start // 60
        start_min = meeting_start % 60
        end_hour = meeting_end // 60
        end_min = meeting_end % 60
        time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
        print(f"Monday {time_str}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()