def main():
    meeting_duration = 30  # minutes

    # Define work hours for Tuesday: 9:00 (540 minutes) to 17:00 (1020 minutes)
    work_start_tue = 9 * 60
    work_end_tue = 17 * 60

    # Margaret's available time on Tuesday: 14:30 (870 minutes) to 17:00 (1020 minutes)
    margaret_start_tue = 14 * 60 + 30
    margaret_end_tue = work_end_tue

    # Alexis's busy intervals on Tuesday (in minutes)
    alexis_busy_tue = [
        (9 * 60, 9 * 60 + 30),      # 9:00-9:30
        (10 * 60, 10 * 60 + 30),    # 10:00-10:30
        (14 * 60, 16 * 60 + 30)     # 14:00-16:30
    ]

    # Function to compute free intervals within a given range
    def get_free_intervals(start, end, busy_intervals):
        # Filter and clip busy intervals to the range [start, end]
        clipped_busy = []
        for bs, be in busy_intervals:
            if be <= start or bs >= end:
                continue
            new_bs = max(bs, start)
            new_be = min(be, end)
            if new_bs < new_be:
                clipped_busy.append((new_bs, new_be))
        # Sort by start time
        clipped_busy.sort(key=lambda x: x[0])
        
        free_intervals = []
        current = start
        for bs, be in clipped_busy:
            if bs > current:
                free_intervals.append((current, bs))
            current = max(current, be)
        if current < end:
            free_intervals.append((current, end))
        return free_intervals

    # Get Alexis's free intervals within Margaret's available time
    free_intervals_alexis = get_free_intervals(margaret_start_tue, margaret_end_tue, alexis_busy_tue)
    
    # Find the first free interval that can accommodate the meeting
    meeting_time = None
    for interval in free_intervals_alexis:
        start_int, end_int = interval
        if end_int - start_int >= meeting_duration:
            meeting_start = start_int
            meeting_end = start_int + meeting_duration
            meeting_time = (meeting_start, meeting_end)
            break

    if meeting_time:
        # Convert minutes to HH:MM format
        def format_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"
        
        start_str = format_time(meeting_time[0])
        end_str = format_time(meeting_time[1])
        time_output = f"{start_str}:{end_str}"
        day_output = "Tuesday"
        
        print(day_output)
        print(time_output)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()