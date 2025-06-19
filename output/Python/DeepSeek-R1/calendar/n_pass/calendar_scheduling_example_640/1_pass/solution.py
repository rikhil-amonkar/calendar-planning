def time_str_to_minutes(time_str):
    h, m = time_str.split(':')
    total_minutes = int(h) * 60 + int(m)
    return total_minutes - 540  # 540 minutes is 9:00

def minutes_to_time_str(minutes_since_9am):
    total_minutes = 540 + minutes_since_9am
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    intervals.sort(key=lambda x: x[0])
    merged = []
    start, end = intervals[0]
    for i in range(1, len(intervals)):
        if intervals[i][0] <= end:
            if intervals[i][1] > end:
                end = intervals[i][1]
        else:
            merged.append((start, end))
            start, end = intervals[i]
    merged.append((start, end))
    return merged

def main():
    bobby_busy = {
        'Monday': [('14:30', '15:00')],
        'Tuesday': [('9:00', '11:30'), ('12:00', '12:30'), ('13:00', '15:00'), ('15:30', '17:00')]
    }
    
    michael_busy = {
        'Monday': [('9:00', '10:00'), ('10:30', '13:30'), ('14:00', '15:00'), ('15:30', '17:00')],
        'Tuesday': [('9:00', '10:30'), ('11:00', '11:30'), ('12:00', '14:00'), ('15:00', '16:00'), ('16:30', '17:00')]
    }
    
    duration = 30  # minutes
    days = ['Monday', 'Tuesday']
    found = False
    day_found = None
    slot_start = None
    
    for day in days:
        intervals = []
        if day in bobby_busy:
            for interval in bobby_busy[day]:
                start_min = time_str_to_minutes(interval[0])
                end_min = time_str_to_minutes(interval[1])
                intervals.append((start_min, end_min))
                
        if day in michael_busy:
            for interval in michael_busy[day]:
                start_min = time_str_to_minutes(interval[0])
                end_min = time_str_to_minutes(interval[1])
                intervals.append((start_min, end_min))
                
        if not intervals:
            free_interval = (0, 480)
            if free_interval[1] - free_interval[0] >= duration:
                day_found = day
                slot_start = free_interval[0]
                found = True
                break
        else:
            merged = merge_intervals(intervals)
            free_intervals = []
            current = 0
            for interval in merged:
                if current < interval[0]:
                    free_intervals.append((current, interval[0]))
                current = interval[1]
            if current < 480:
                free_intervals.append((current, 480))
                
            for free in free_intervals:
                if free[1] - free[0] >= duration:
                    day_found = day
                    slot_start = free[0]
                    found = True
                    break
            if found:
                break
                
    if found:
        start_time = minutes_to_time_str(slot_start)
        end_time = minutes_to_time_str(slot_start + duration)
        time_output = f"{start_time}:{end_time}"
        print(day_found)
        print(time_output)
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()