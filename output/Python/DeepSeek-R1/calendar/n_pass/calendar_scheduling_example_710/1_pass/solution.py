def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return (hour - 9) * 60 + minute

def compute_free_intervals(busy_list, day_start=0, day_end=480):
    free_intervals = [(day_start, day_end)]
    if not busy_list:
        return free_intervals
        
    busy_intervals = []
    for (s, e) in busy_list:
        s_min = time_to_minutes(s)
        e_min = time_to_minutes(e)
        busy_intervals.append((s_min, e_min))
    
    busy_intervals.sort(key=lambda x: x[0])
    
    for (s, e) in busy_intervals:
        new_free = []
        for (start, end) in free_intervals:
            if end <= s or start >= e:
                new_free.append((start, end))
            else:
                if start < s:
                    new_free.append((start, s))
                if end > e:
                    new_free.append((e, end))
        free_intervals = new_free
    return free_intervals

def intersect_intervals(intervals1, intervals2):
    common = []
    for (s1, e1) in intervals1:
        for (s2, e2) in intervals2:
            low = max(s1, s2)
            high = min(e1, e2)
            if low < high:
                common.append((low, high))
    return common

def main():
    days = ['Monday', 'Tuesday']
    
    cheryl_busy = {
        'Monday': [('9:00', '9:30'), ('11:30', '13:00'), ('15:30', '16:00')],
        'Tuesday': [('15:00', '15:30')]
    }
    
    kyle_busy = {
        'Monday': [('9:00', '17:00')],
        'Tuesday': [('9:30', '17:00')]
    }
    
    for day in days:
        cheryl_free = compute_free_intervals(cheryl_busy.get(day, []))
        kyle_free = compute_free_intervals(kyle_busy.get(day, []))
        common_free = intersect_intervals(cheryl_free, kyle_free)
        
        for (start, end) in common_free:
            if end - start >= 30:
                start_minutes = start
                end_minutes = start_minutes + 30
                
                start_hour = 9 + start_minutes // 60
                start_minute = start_minutes % 60
                end_hour = 9 + end_minutes // 60
                end_minute = end_minutes % 60
                
                time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
                print(day)
                print(time_str)
                return
                
    print("No suitable time found")

if __name__ == "__main__":
    main()