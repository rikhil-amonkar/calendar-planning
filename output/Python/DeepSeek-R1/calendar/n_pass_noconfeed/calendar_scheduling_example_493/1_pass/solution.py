def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 30

    participants = {
        'Tyler': [],
        'Kelly': [],
        'Stephanie': ["11:00 to 11:30", "14:30 to 15:00"],
        'Hannah': [],
        'Joe': ["9:00 to 9:30", "10:00 to 12:00", "12:30 to 13:00", "14:00 to 17:00"],
        'Diana': ["9:00 to 10:30", "11:30 to 12:00", "13:00 to 14:00", "14:30 to 15:30", "16:00 to 17:00"],
        'Deborah': ["9:00 to 10:00", "10:30 to 12:00", "12:30 to 13:00", "13:30 to 14:00", "14:30 to 15:30", "16:00 to 16:30"]
    }

    busy_intervals = []
    for name, intervals in participants.items():
        for interval in intervals:
            parts = interval.split(' to ')
            if len(parts) != 2:
                continue
            start_str, end_str = parts[0].strip(), parts[1].strip()
            start_min = time_to_minutes(start_str)
            end_min = time_to_minutes(end_str)
            busy_intervals.append((start_min, end_min))
    
    if not busy_intervals:
        merged = []
    else:
        busy_intervals.sort(key=lambda x: x[0])
        merged = []
        current_start, current_end = busy_intervals[0]
        for interval in busy_intervals[1:]:
            s, e = interval
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))
    
    free_intervals = []
    if not merged:
        free_intervals.append((work_start, work_end))
    else:
        if work_start < merged[0][0]:
            free_intervals.append((work_start, merged[0][0]))
        for i in range(len(merged) - 1):
            gap_start = merged[i][1]
            gap_end = merged[i+1][0]
            if gap_start < gap_end:
                free_intervals.append((gap_start, gap_end))
        if merged[-1][1] < work_end:
            free_intervals.append((merged[-1][1], work_end))
    
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            start_time = minutes_to_time(meeting_start)
            end_time = minutes_to_time(meeting_end)
            print("Monday")
            print(f"{start_time}:{end_time}")
            return

if __name__ == "__main__":
    main()