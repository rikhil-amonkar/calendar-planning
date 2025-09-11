def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    duration = 60
    
    natalie_busy = {
        "Monday": ["9:00-9:30", "10:00-12:00", "12:30-13:00", "14:00-14:30", "15:00-16:30"],
        "Tuesday": ["9:00-9:30", "10:00-10:30", "12:30-14:00", "16:00-17:00"],
        "Wednesday": ["11:00-11:30", "16:00-16:30"],
        "Thursday": ["10:00-11:00", "11:30-15:00", "15:30-16:00", "16:30-17:00"]
    }
    
    william_busy = {
        "Monday": ["9:30-11:00", "11:30-17:00"],
        "Tuesday": ["9:00-13:00", "13:30-16:00"],
        "Wednesday": ["9:00-12:30", "13:00-14:30", "15:30-16:00", "16:30-17:00"],
        "Thursday": ["9:00-10:30", "11:00-11:30", "12:00-12:30", "13:00-14:00", "15:00-17:00"]
    }
    
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    
    for day in days:
        intervals = []
        for busy_str in natalie_busy[day]:
            start_str, end_str = busy_str.split('-')
            start_min = time_to_minutes(start_str)
            end_min = time_to_minutes(end_str)
            intervals.append((start_min, end_min))
        
        for busy_str in william_busy[day]:
            start_str, end_str = busy_str.split('-')
            start_min = time_to_minutes(start_str)
            end_min = time_to_minutes(end_str)
            intervals.append((start_min, end_min))
        
        intervals.sort(key=lambda x: x[0])
        
        merged = []
        for start, end in intervals:
            if not merged:
                merged.append([start, end])
            else:
                last_start, last_end = merged[-1]
                if start <= last_end:
                    merged[-1][1] = max(last_end, end)
                else:
                    merged.append([start, end])
        
        free_start = work_start
        free_intervals = []
        for start, end in merged:
            if free_start < start:
                free_intervals.append((free_start, start))
            free_start = max(free_start, end)
        if free_start < work_end:
            free_intervals.append((free_start, work_end))
        
        for start_free, end_free in free_intervals:
            if end_free - start_free >= duration:
                meeting_start = start_free
                meeting_end = meeting_start + duration
                start_time_str = minutes_to_time(meeting_start)
                end_time_str = minutes_to_time(meeting_end)
                print(f"{day} {start_time_str}:{end_time_str}")
                return
    
    print("No suitable time found.")

if __name__ == "__main__":
    main()