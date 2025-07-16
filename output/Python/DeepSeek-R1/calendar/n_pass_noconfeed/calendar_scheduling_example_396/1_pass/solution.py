def main():
    work_start_min = 9 * 60  # 9:00 in minutes
    work_end_min = 17 * 60   # 17:00 in minutes
    meeting_duration = 30    # minutes

    # Convert time string to minutes
    def time_str_to_minutes(time_str):
        parts = time_str.split(':')
        return int(parts[0]) * 60 + int(parts[1])

    # Define busy intervals for each participant
    participants_busy = {
        'Andrea': [],
        'Jack': [("9:00", "9:30"), ("14:00", "14:30")],
        'Madison': [("9:30", "10:30"), ("13:00", "14:00"), ("15:00", "15:30"), ("16:30", "17:00")],
        'Rachel': [("9:30", "10:30"), ("11:00", "11:30"), ("12:00", "13:30"), ("14:30", "15:30"), ("16:00", "17:00")],
        'Douglas': [("9:00", "11:30"), ("12:00", "16:30")],
        'Ryan': [("9:00", "9:30"), ("13:00", "14:00"), ("14:30", "17:00")]
    }

    # Collect all busy intervals in minutes
    all_busy = []
    for person, intervals in participants_busy.items():
        for interval in intervals:
            start_min = time_str_to_minutes(interval[0])
            end_min = time_str_to_minutes(interval[1])
            all_busy.append((start_min, end_min))
    
    # Sort intervals by start time
    all_busy.sort(key=lambda x: x[0])
    
    # Merge intervals
    merged_busy = []
    if all_busy:
        merged_busy = [all_busy[0]]
        for i in range(1, len(all_busy)):
            current = all_busy[i]
            last = merged_busy[-1]
            if current[0] <= last[1]:
                merged_busy[-1] = (last[0], max(last[1], current[1]))
            else:
                merged_busy.append(current)
    
    # Find free gaps
    gaps = []
    current_start = work_start_min
    for busy_interval in merged_busy:
        if busy_interval[0] > current_start:
            gap_duration = busy_interval[0] - current_start
            if gap_duration >= meeting_duration:
                gaps.append((current_start, busy_interval[0]))
        current_start = max(current_start, busy_interval[1])
    
    # Check after the last busy interval
    if current_start < work_end_min:
        gap_duration = work_end_min - current_start
        if gap_duration >= meeting_duration:
            gaps.append((current_start, work_end_min))
    
    # Select the first gap
    if gaps:
        gap_start, gap_end = gaps[0]
        meeting_start = gap_start
        meeting_end = meeting_start + meeting_duration
        
        # Convert meeting times back to HH:MM format
        def min_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"
        
        start_str = min_to_time(meeting_start)
        end_str = min_to_time(meeting_end)
        
        print("Monday")
        print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()