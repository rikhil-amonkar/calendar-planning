def main():
    # Define work hours in minutes from midnight (9:00=540, 17:00=1020)
    work_start = 540
    work_end = 1020
    meeting_duration = 30
    
    # Busy intervals for each participant (start, end) in minutes
    participants_busy = {
        'Joe': [(570, 600), (630, 660)],
        'Keith': [(690, 720), (900, 930)],
        'Patricia': [(540, 570), (780, 810)],
        'Nancy': [(540, 660), (690, 990)],
        'Pamela': [(540, 600), (630, 660), (690, 750), (780, 840), (870, 900), (930, 960), (990, 1020)]
    }
    
    # Function to compute free intervals within work hours
    def get_free_intervals(busy_list, start_bound, end_bound):
        if not busy_list:
            return [(start_bound, end_bound)]
        sorted_busy = sorted(busy_list, key=lambda x: x[0])
        free = []
        current_start = start_bound
        for start, end in sorted_busy:
            if current_start < start:
                free.append((current_start, start))
            current_start = max(current_start, end)
        if current_start < end_bound:
            free.append((current_start, end_bound))
        return free
    
    # Function to intersect two sets of intervals
    def intersect_intervals(intervals1, intervals2):
        result = []
        for (s1, e1) in intervals1:
            for (s2, e2) in intervals2:
                start_overlap = max(s1, s2)
                end_overlap = min(e1, e2)
                if start_overlap < end_overlap:
                    result.append((start_overlap, end_overlap))
        return result
    
    # Calculate free intervals for each participant
    free_intervals = []
    for busy in participants_busy.values():
        free_intervals.append(get_free_intervals(busy, work_start, work_end))
    
    # Find common free intervals
    common_free = free_intervals[0]
    for i in range(1, len(free_intervals)):
        common_free = intersect_intervals(common_free, free_intervals[i])
    
    # Sort to find earliest interval
    common_free_sorted = sorted(common_free, key=lambda x: x[0])
    
    # Find the first common free interval with sufficient duration
    meeting_start = None
    for start, end in common_free_sorted:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            break
    
    # Convert minutes to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02d}:{minutes:02d}"
    
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    
    # Output day and time in HH:MM:HH:MM format
    print("Monday")
    print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()