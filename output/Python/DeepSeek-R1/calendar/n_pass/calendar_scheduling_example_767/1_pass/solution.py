def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return (hour - 9) * 60 + minute

def minutes_to_time_string(start_minutes, end_minutes):
    start_hour = 9 + start_minutes // 60
    start_min = start_minutes % 60
    end_hour = 9 + end_minutes // 60
    end_min = end_minutes % 60
    return f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"

def compute_free_intervals(busy_intervals):
    if not busy_intervals:
        return [[0, 480]]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    merged = []
    current_start, current_end = sorted_busy[0]
    for i in range(1, len(sorted_busy)):
        s, e = sorted_busy[i]
        if s <= current_end:
            current_end = max(current_end, e)
        else:
            merged.append([current_start, current_end])
            current_start, current_end = s, e
    merged.append([current_start, current_end])
    
    free_intervals = []
    current = 0
    for interval in merged:
        if current < interval[0]:
            free_intervals.append([current, interval[0]])
        current = interval[1]
    if current < 480:
        free_intervals.append([current, 480])
    return free_intervals

def main():
    days = ['Monday', 'Tuesday', 'Wednesday']
    martha_busy = {
        'Monday': [('16:00', '17:00')],
        'Tuesday': [('15:00', '15:30')],
        'Wednesday': [('10:00', '11:00'), ('14:00', '14:30')]
    }
    beverly_busy = {
        'Monday': [('9:00', '13:30'), ('14:00', '17:00')],
        'Tuesday': [('9:00', '17:00')],
        'Wednesday': [('9:30', '15:30'), ('16:30', '17:00')]
    }
    
    for day in days:
        mar_busy_today = martha_busy.get(day, [])
        bev_busy_today = beverly_busy.get(day, [])
        
        mar_busy_min = []
        for (s, e) in mar_busy_today:
            s_min = time_str_to_minutes(s)
            e_min = time_str_to_minutes(e)
            mar_busy_min.append([s_min, e_min])
        
        bev_busy_min = []
        for (s, e) in bev_busy_today:
            s_min = time_str_to_minutes(s)
            e_min = time_str_to_minutes(e)
            bev_busy_min.append([s_min, e_min])
        
        mar_free = compute_free_intervals(mar_busy_min)
        bev_free = compute_free_intervals(bev_busy_min)
        
        common_free = []
        for iv_mar in mar_free:
            for iv_bev in bev_free:
                start_common = max(iv_mar[0], iv_bev[0])
                end_common = min(iv_mar[1], iv_bev[1])
                if start_common < end_common:
                    common_free.append([start_common, end_common])
        
        for interval in common_free:
            duration = interval[1] - interval[0]
            if duration >= 60:
                meeting_start = interval[0]
                meeting_end = meeting_start + 60
                time_str = minutes_to_time_string(meeting_start, meeting_end)
                print(day)
                print(time_str)
                return
                
    print("No suitable time found")

if __name__ == "__main__":
    main()