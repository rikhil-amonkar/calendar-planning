def main():
    work_start_minutes = 9 * 60  # 540 minutes (9:00)
    work_end_minutes = 17 * 60    # 1020 minutes (17:00)
    meeting_duration = 30

    # Busy intervals for each participant
    participants_busy = {
        "Gregory": ["9:00 to 9:30", "11:30 to 12:00"],
        "Jonathan": ["9:00 to 9:30", "12:00 to 12:30", "13:00 to 13:30", "15:00 to 16:00", "16:30 to 17:00"],
        "Barbara": ["10:00 to 10:30", "13:30 to 14:00"],
        "Jesse": ["10:00 to 11:00", "12:30 to 14:30"],
        "Alan": ["9:30 to 11:00", "11:30 to 12:30", "13:00 to 15:30", "16:00 to 17:00"],
        "Nicole": ["9:00 to 10:30", "11:30 to 12:00", "12:30 to 13:30", "14:00 to 17:00"],
        "Catherine": ["9:00 to 10:30", "12:00 to 13:30", "15:00 to 15:30", "16:00 to 16:30"]
    }

    def time_str_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return hour * 60 + minute

    all_busy = []
    for person, intervals in participants_busy.items():
        for interval in intervals:
            start_str, end_str = interval.split(' to ')
            start_minutes = time_str_to_minutes(start_str)
            end_minutes = time_str_to_minutes(end_str)
            all_busy.append((start_minutes, end_minutes))
    
    if not all_busy:
        # If no busy intervals, schedule at the start of the day
        meeting_start = work_start_minutes
        meeting_end = meeting_start + meeting_duration
        start_hour = meeting_start // 60
        start_minute = meeting_start % 60
        end_hour = meeting_end // 60
        end_minute = meeting_end % 60
        start_str = f"{start_hour}:{start_minute:02d}"
        end_str = f"{end_hour}:{end_minute:02d}"
        print(f"Monday {start_str}:{end_str}")
        return

    all_busy.sort(key=lambda x: x[0])
    merged = []
    current_start, current_end = all_busy[0]
    for i in range(1, len(all_busy)):
        s, e = all_busy[i]
        if s <= current_end:
            current_end = max(current_end, e)
        else:
            merged.append((current_start, current_end))
            current_start, current_end = s, e
    merged.append((current_start, current_end))

    free_intervals = []
    # Before the first busy interval?
    if work_start_minutes < merged[0][0]:
        free_intervals.append((work_start_minutes, merged[0][0]))
    
    for i in range(len(merged) - 1):
        free_start = merged[i][1]
        free_end = merged[i+1][0]
        if free_start < free_end:
            free_intervals.append((free_start, free_end))
    
    if merged[-1][1] < work_end_minutes:
        free_intervals.append((merged[-1][1], work_end_minutes))
    
    found = False
    for free_start, free_end in free_intervals:
        if free_end - free_start >= meeting_duration:
            meeting_start = free_start
            meeting_end = meeting_start + meeting_duration
            start_hour = meeting_start // 60
            start_minute = meeting_start % 60
            end_hour = meeting_end // 60
            end_minute = meeting_end % 60
            start_str = f"{start_hour}:{start_minute:02d}"
            end_str = f"{end_hour}:{end_minute:02d}"
            found = True
            break
    
    if found:
        print(f"Monday {start_str}:{end_str}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()