def time_str_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Define work hours in minutes (9:00 to 17:00)
    work_start = 9 * 60  # 540 minutes
    work_end = 17 * 60   # 1020 minutes
    duration = 60  # 60 minutes for the meeting

    # Brian's busy schedule
    brian_busy = {
        'Monday': [('9:30','10:00'), ('12:30','14:30'), ('15:30','16:00')],
        'Tuesday': [('9:00','9:30')],
        'Wednesday': [('12:30','14:00'), ('16:30','17:00')],
        'Thursday': [('11:00','11:30'), ('13:00','13:30'), ('16:30','17:00')],
        'Friday': [('9:30','10:00'), ('10:30','11:00'), ('13:00','13:30'), ('15:00','16:00'), ('16:30','17:00')]
    }

    # Julia's busy schedule
    julia_busy = {
        'Monday': [('9:00','10:00'), ('11:00','11:30'), ('12:30','13:00'), ('15:30','16:00')],
        'Tuesday': [('13:00','14:00'), ('16:00','16:30')],
        'Wednesday': [('9:00','11:30'), ('12:00','12:30'), ('13:00','17:00')],
        'Thursday': [('9:00','10:30'), ('11:00','17:00')],
        'Friday': [('9:00','10:00'), ('10:30','11:30'), ('12:30','14:00'), ('14:30','15:00'), ('15:30','16:00')]
    }

    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    meeting_found = False
    meeting_day = None
    meeting_start_minutes = None

    for day in days:
        intervals = []
        
        # Process Brian's busy intervals for the day
        if day in brian_busy:
            for interval in brian_busy[day]:
                start_min = time_str_to_minutes(interval[0])
                end_min = time_str_to_minutes(interval[1])
                intervals.append((start_min, end_min))
        
        # Process Julia's busy intervals for the day
        if day in julia_busy:
            for interval in julia_busy[day]:
                start_min = time_str_to_minutes(interval[0])
                end_min = time_str_to_minutes(interval[1])
                intervals.append((start_min, end_min))
        
        # If no intervals, the whole day is free
        if not intervals:
            # Check if the entire work day is long enough
            if work_end - work_start >= duration:
                meeting_start_minutes = work_start
                meeting_day = day
                meeting_found = True
                break
        
        # Sort intervals by start time
        intervals.sort(key=lambda x: x[0])
        merged = []
        if intervals:
            start_curr, end_curr = intervals[0]
            for i in range(1, len(intervals)):
                s, e = intervals[i]
                if s <= end_curr:
                    if e > end_curr:
                        end_curr = e
                else:
                    merged.append((start_curr, end_curr))
                    start_curr, end_curr = s, e
            merged.append((start_curr, end_curr))
        
        # Calculate free intervals
        free_intervals = []
        current = work_start
        for s, e in merged:
            if current < s:
                free_intervals.append((current, s))
            current = max(current, e)
        if current < work_end:
            free_intervals.append((current, work_end))
        
        # Check free intervals for a slot of at least 'duration'
        for start_free, end_free in free_intervals:
            if end_free - start_free >= duration:
                meeting_start_minutes = start_free
                meeting_day = day
                meeting_found = True
                break
        if meeting_found:
            break
    
    if meeting_found:
        meeting_end_minutes = meeting_start_minutes + duration
        start_h = meeting_start_minutes // 60
        start_m = meeting_start_minutes % 60
        end_h = meeting_end_minutes // 60
        end_m = meeting_end_minutes % 60
        time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
        print(meeting_day)
        print(time_str)

if __name__ == "__main__":
    main()