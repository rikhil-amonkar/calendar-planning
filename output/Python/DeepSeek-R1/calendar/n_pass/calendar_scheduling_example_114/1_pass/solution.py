def main():
    # Define work hours (9:00 to 17:00) in minutes from 9:00
    work_start = 0   # 9:00
    work_end = 480   # 17:00
    meeting_duration = 60  # 1 hour

    # Busy intervals for each participant (in minutes from 9:00)
    all_busy = [
        # Stephanie
        (60, 90), (420, 450),
        # Cheryl
        (60, 90), (150, 180), (270, 300), (450, 480),
        # Bradley
        (30, 60), (90, 150), (270, 300), (330, 360), (390, 480),
        # Steven
        (0, 180), (240, 270), (330, 480)
    ]

    # Aggregate events: +1 for start, -1 for end
    events_aggregated = {}
    for s, e in all_busy:
        events_aggregated[s] = events_aggregated.get(s, 0) + 1
        events_aggregated[e] = events_aggregated.get(e, 0) - 1

    # Sort event times
    event_times = sorted(events_aggregated.keys())
    counter = 0
    free_start = work_start
    free_intervals = []
    
    # Track free intervals
    for time in event_times:
        net_delta = events_aggregated[time]
        prev_counter = counter
        counter += net_delta
        
        if prev_counter == 0 and counter > 0:
            if time > free_start:
                free_intervals.append((free_start, time))
            free_start = None
        if prev_counter > 0 and counter == 0:
            free_start = time
    
    # Add last free interval if applicable
    if free_start is not None and free_start < work_end:
        free_intervals.append((free_start, work_end))
    
    # Find first free interval that fits the meeting
    meeting_slot = None
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_slot = (start, start + meeting_duration)
            break
    
    if meeting_slot:
        start_min, end_min = meeting_slot
        # Convert start time to HH:MM
        start_hour = 9 + start_min // 60
        start_minute = start_min % 60
        start_str = f"{start_hour:02d}:{start_minute:02d}"
        
        # Convert end time to HH:MM
        end_hour = 9 + end_min // 60
        end_minute = end_min % 60
        end_str = f"{end_hour:02d}:{end_minute:02d}"
        
        # Output day and time range
        print("Monday")
        print(f"{start_str}:{end_str}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()