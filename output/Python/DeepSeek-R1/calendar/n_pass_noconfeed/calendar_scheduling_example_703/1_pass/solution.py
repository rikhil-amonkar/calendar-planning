def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(mins):
    h, m = divmod(mins, 60)
    return f"{h:02d}:{m:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for current in intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def main():
    stephanie_schedule = {
        'Monday': [('9:30','10:00'), ('10:30','11:00'), ('11:30','12:00'), ('14:00','14:30')],
        'Tuesday': [('12:00','13:00')],
        'Wednesday': [('9:00','10:00'), ('13:00','14:00')]
    }
    
    betty_schedule = {
        'Monday': [('9:00','10:00'), ('11:00','11:30'), ('14:30','15:00'), ('15:30','16:00')],
        'Tuesday': [('9:00','9:30'), ('11:30','12:00'), ('12:30','14:30'), ('15:30','16:00')],
        'Wednesday': [('10:00','11:30'), ('12:00','14:00'), ('14:30','17:00')]
    }
    
    work_start = time_to_minutes('9:00')
    days = ['Tuesday', 'Wednesday', 'Monday']
    meeting_duration = 60
    
    for day in days:
        if day == 'Tuesday':
            work_end = time_to_minutes('12:30')
        else:
            work_end = time_to_minutes('17:00')
        
        busy_intervals = []
        for meet in stephanie_schedule.get(day, []):
            s, e = meet
            busy_intervals.append((time_to_minutes(s), time_to_minutes(e)))
        for meet in betty_schedule.get(day, []):
            s, e = meet
            busy_intervals.append((time_to_minutes(s), time_to_minutes(e)))
        
        if not busy_intervals:
            free_intervals = [(work_start, work_end)]
        else:
            merged = merge_intervals(busy_intervals)
            free_intervals = []
            current = work_start
            for start, end in merged:
                if current < start:
                    free_intervals.append((current, start))
                current = max(current, end)
            if current < work_end:
                free_intervals.append((current, work_end))
        
        for start, end in free_intervals:
            if end - start >= meeting_duration:
                meeting_start = start
                meeting_end = start + meeting_duration
                start_str = minutes_to_time(meeting_start)
                end_str = minutes_to_time(meeting_end)
                print(day)
                print(f"{start_str}:{end_str}")
                return
    
    # Fallback if no slot found (shouldn't happen per problem)
    print("No suitable time found")

if __name__ == "__main__":
    main()