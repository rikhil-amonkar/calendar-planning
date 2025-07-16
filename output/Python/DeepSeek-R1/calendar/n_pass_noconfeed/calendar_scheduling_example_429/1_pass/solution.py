def main():
    participants = {
        "Judy": ["13:00-13:30", "16:00-16:30"],
        "Olivia": ["10:00-10:30", "12:00-13:00", "14:00-14:30"],
        "Eric": [],
        "Jacqueline": ["10:00-10:30", "15:00-15:30"],
        "Laura": ["9:00-10:00", "10:30-12:00", "13:00-13:30", "14:30-15:00", "15:30-17:00"],
        "Tyler": ["9:00-10:00", "11:00-11:30", "12:30-13:00", "14:00-14:30", "15:30-17:00"],
        "Lisa": ["9:30-10:30", "11:00-11:30", "12:00-12:30", "13:00-13:30", "14:00-14:30", "16:00-17:00"]
    }
    
    work_start_minutes = 9 * 60  # 9:00
    work_end_minutes = 17 * 60   # 17:00
    meeting_duration = 30        # minutes
    
    def time_str_to_minutes(time_str):
        parts = time_str.split(':')
        hours = int(parts[0])
        minutes = int(parts[1])
        return hours * 60 + minutes

    busy_intervals = []
    for person, intervals in participants.items():
        for interval in intervals:
            start_str, end_str = interval.split('-')
            start_minutes = time_str_to_minutes(start_str)
            end_minutes = time_str_to_minutes(end_str)
            busy_intervals.append((start_minutes, end_minutes))
    
    if not busy_intervals:
        free_interval_start = work_start_minutes
        meeting_start = free_interval_start
        meeting_end_minutes = meeting_start + meeting_duration
        start_hour = meeting_start // 60
        start_minute = meeting_start % 60
        end_hour = meeting_end_minutes // 60
        end_minute = meeting_end_minutes % 60
        time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print("Monday")
        print(time_str)
        return

    busy_intervals.sort(key=lambda x: x[0])
    merged = []
    current_start, current_end = busy_intervals[0]
    for i in range(1, len(busy_intervals)):
        interval = busy_intervals[i]
        if interval[0] <= current_end:
            if interval[1] > current_end:
                current_end = interval[1]
        else:
            merged.append((current_start, current_end))
            current_start, current_end = interval
    merged.append((current_start, current_end))
    
    free_intervals = []
    current = work_start_minutes
    for start, end in merged:
        if current < start:
            free_intervals.append((current, start))
        current = max(current, end)
        if current >= work_end_minutes:
            break
    if current < work_end_minutes:
        free_intervals.append((current, work_end_minutes))
    
    for start, end in free_intervals:
        duration = end - start
        if duration >= meeting_duration:
            meeting_start = start
            meeting_end_minutes = meeting_start + meeting_duration
            start_hour = meeting_start // 60
            start_minute = meeting_start % 60
            end_hour = meeting_end_minutes // 60
            end_minute = meeting_end_minutes % 60
            time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
            print("Monday")
            print(time_str)
            return

    print("No suitable time found")

if __name__ == "__main__":
    main()