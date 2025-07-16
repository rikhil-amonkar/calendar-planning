def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1]) if len(parts) > 1 else 0
    return hours * 60 + minutes

def main():
    james_busy = {
        'Monday': ['9:00 to 9:30', '10:30 to 11:00', '12:30 to 13:00', '14:30 to 15:30', '16:30 to 17:00'],
        'Tuesday': ['9:00 to 11:00', '11:30 to 12:00', '12:30 to 15:30', '16:00 to 17:00'],
        'Wednesday': ['10:00 to 11:00', '12:00 to 13:00', '13:30 to 16:00'],
        'Thursday': ['9:30 to 11:30', '12:00 to 12:30', '13:00 to 13:30', '14:00 to 14:30', '16:30 to 17:00']
    }
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    work_start = 9 * 60
    work_end = 17 * 60
    duration = 30

    for day in days:
        busy_intervals = []
        if day in james_busy:
            for interval in james_busy[day]:
                tokens = interval.split()
                start_min = time_to_minutes(tokens[0])
                end_min = time_to_minutes(tokens[2])
                busy_intervals.append((start_min, end_min))
        
        if busy_intervals:
            busy_intervals.sort(key=lambda x: x[0])
            merged_busy = []
            current_start, current_end = busy_intervals[0]
            for i in range(1, len(busy_intervals)):
                s, e = busy_intervals[i]
                if s <= current_end:
                    current_end = max(current_end, e)
                else:
                    merged_busy.append((current_start, current_end))
                    current_start, current_end = s, e
            merged_busy.append((current_start, current_end))
        else:
            merged_busy = []
        
        free_intervals = []
        current = work_start
        for s, e in merged_busy:
            if current < s:
                free_intervals.append((current, s))
            current = max(current, e)
        if current < work_end:
            free_intervals.append((current, work_end))
        
        for start, end in free_intervals:
            if end - start >= duration:
                meeting_start = start
                meeting_end = start + duration
                start_h = meeting_start // 60
                start_m = meeting_start % 60
                end_h = meeting_end // 60
                end_m = meeting_end % 60
                time_range_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
                print(day)
                print(time_range_str)
                return
                
    print("No suitable time found")

if __name__ == "__main__":
    main()