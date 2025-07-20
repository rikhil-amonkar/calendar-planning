def main():
    # Meeting duration in minutes
    duration = 30
    # Work hours: 9:00 to 17:00 -> 0 to 480 minutes
    max_global_time = 480
    # Harold's constraint: meeting must end by 13:00 (240 minutes from 9:00)
    max_time = 240

    # Busy intervals for each participant in minutes (start, end) - end is exclusive
    jacqueline = [(0, 30), (120, 150), (210, 240), (390, 420)]
    harold = [(60, 90), (240, 270), (360, 480)]
    arthur = [(0, 30), (60, 210), (330, 360), (390, 480)]
    kelly = [(0, 30), (60, 120), (150, 210), (300, 360), (390, 420)]
    
    participants = [jacqueline, harold, arthur, kelly]
    
    # Collect all busy intervals that start before max_time (240 minutes) and clip to [0, max_time]
    all_busy = []
    for person in participants:
        for interval in person:
            s, e = interval
            if s >= max_time:
                continue
            end_clipped = min(e, max_time)
            if s < end_clipped:
                all_busy.append((s, end_clipped))
    
    # If there are no busy intervals, the entire [0, max_time] is free
    if not all_busy:
        merged_busy = []
    else:
        all_busy.sort(key=lambda x: x[0])
        merged_busy = [all_busy[0]]
        for i in range(1, len(all_busy)):
            current_start, current_end = all_busy[i]
            last_start, last_end = merged_busy[-1]
            if current_start <= last_end:
                merged_busy[-1] = (last_start, max(last_end, current_end))
            else:
                merged_busy.append((current_start, current_end))
    
    # Compute free intervals in [0, max_time]
    free_intervals = []
    current_start_free = 0
    for interval in merged_busy:
        s_busy, e_busy = interval
        if current_start_free < s_busy:
            free_intervals.append((current_start_free, s_busy))
        current_start_free = e_busy
    if current_start_free < max_time:
        free_intervals.append((current_start_free, max_time))
    
    # Find the first free interval that can fit the meeting duration
    meeting_start = None
    for interval in free_intervals:
        s_free, e_free = interval
        if e_free - s_free >= duration:
            meeting_start = s_free
            break
    
    if meeting_start is None:
        # According to the problem, there is a solution, so this should not happen.
        print("No suitable time found")
    else:
        meeting_end = meeting_start + duration
        # Convert start time
        start_hour = 9 + meeting_start // 60
        start_minute = meeting_start % 60
        # Convert end time
        end_hour = 9 + meeting_end // 60
        end_minute = meeting_end % 60
        # Format as HH:MM:HH:MM
        time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print("Monday")
        print(time_str)

if __name__ == "__main__":
    main()