def main():
    work_start = "9:00"
    work_end = "17:00"
    day = "Monday"
    meeting_duration = 60  # minutes

    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hours = int(parts[0])
        minutes = int(parts[1])
        return (hours - 9) * 60 + minutes

    def minutes_to_time(total_minutes):
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    work_end_min = time_to_minutes(work_end)

    kayla_busy = [("10:00", "10:30"), ("14:30", "16:00")]
    rebecca_busy = [("9:00", "13:00"), ("13:30", "15:00"), ("15:30", "16:00")]

    all_busy = []
    for interval in kayla_busy:
        start_min = time_to_minutes(interval[0])
        end_min = time_to_minutes(interval[1])
        all_busy.append((start_min, end_min))
    
    for interval in rebecca_busy:
        start_min = time_to_minutes(interval[0])
        end_min = time_to_minutes(interval[1])
        all_busy.append((start_min, end_min))
    
    all_busy.sort(key=lambda x: x[0])
    
    merged_busy = []
    if all_busy:
        current_start, current_end = all_busy[0]
        for i in range(1, len(all_busy)):
            s, e = all_busy[i]
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged_busy.append((current_start, current_end))
                current_start, current_end = s, e
        merged_busy.append((current_start, current_end))
    
    free_intervals = []
    start_free = 0
    for busy_interval in merged_busy:
        if busy_interval[0] > start_free:
            free_intervals.append((start_free, busy_interval[0]))
        start_free = busy_interval[1]
    if start_free < work_end_min:
        free_intervals.append((start_free, work_end_min))
    
    meeting_time = None
    for interval in free_intervals:
        start, end = interval
        if end - start >= meeting_duration:
            meeting_start_min = start
            meeting_end_min = start + meeting_duration
            start_str = minutes_to_time(meeting_start_min)
            end_str = minutes_to_time(meeting_end_min)
            meeting_time = f"{day} {start_str}:{end_str}"
            break
    
    if meeting_time:
        print(meeting_time)
    else:
        print("No suitable time found.")

if __name__ == "__main__":
    main()