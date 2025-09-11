def main():
    # Define work hours in minutes from 9:00 (0) to 17:00 (480)
    work_start = 0
    work_end = 480
    meeting_duration = 30
    
    # Jack's busy intervals in minutes from 9:00
    jack_busy = [
        (30, 90),   # 9:30-10:30
        (120, 150), # 11:00-11:30
        (210, 240), # 12:30-13:00
        (300, 330), # 14:00-14:30
        (420, 450)  # 16:00-16:30
    ]
    
    # Charlotte's busy intervals in minutes from 9:00
    charlotte_busy = [
        (30, 60),   # 9:30-10:00
        (90, 180),  # 10:30-12:00
        (210, 270), # 12:30-13:30
        (300, 420)  # 14:00-16:00
    ]
    
    # Function to calculate free intervals given busy intervals and work boundaries
    def get_free_intervals(busy_intervals, start, end):
        free_intervals = []
        busy_sorted = sorted(busy_intervals, key=lambda x: x[0])
        current = start
        
        for busy in busy_sorted:
            if current < busy[0]:
                free_intervals.append((current, busy[0]))
            current = max(current, busy[1])
        if current < end:
            free_intervals.append((current, end))
        return free_intervals
    
    # Get free intervals for Jack and Charlotte
    jack_free = get_free_intervals(jack_busy, work_start, work_end)
    charlotte_free = get_free_intervals(charlotte_busy, work_start, work_end)
    
    # Find common free intervals
    common_free = []
    for j_start, j_end in jack_free:
        for c_start, c_end in charlotte_free:
            start = max(j_start, c_start)
            end = min(j_end, c_end)
            if start < end:
                common_free.append((start, end))
    
    # Jack's preference: avoid meetings starting after 12:30 (210 minutes from 9:00)
    preference_cutoff = 210
    
    # Find the earliest common free interval that meets duration and preference
    proposed_interval = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            # Check if the meeting can be scheduled without starting after preference_cutoff
            if start + meeting_duration <= preference_cutoff:
                proposed_interval = (start, start + meeting_duration)
                break
    # If no interval found meeting preference, use the first available
    if proposed_interval is None:
        for start, end in common_free:
            if end - start >= meeting_duration:
                proposed_interval = (start, start + meeting_duration)
                break
    
    # Convert minutes back to time string HH:MM
    def minutes_to_time(minutes):
        hours = 9 + minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    start_time = minutes_to_time(proposed_interval[0])
    end_time = minutes_to_time(proposed_interval[1])
    
    # Output the day and time range in specified format
    print(f"Monday {{{start_time}:{end_time}}}")

if __name__ == "__main__":
    main()