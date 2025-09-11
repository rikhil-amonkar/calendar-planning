def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return (hours - 9) * 60 + minutes

def minutes_to_time(minutes):
    hours = 9 + minutes // 60
    minutes = minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy_intervals, day_start=0, day_end=480):
    intervals = []
    busy_list = []
    for busystr in busy_intervals:
        start_str, end_str = busystr.split('-')
        start_min = time_to_minutes(start_str)
        end_min = time_to_minutes(end_str)
        busy_list.append([start_min, end_min])
    
    busy_list.sort(key=lambda x: x[0])
    
    free_list = []
    current = day_start
    for busy in busy_list:
        if current < busy[0]:
            free_list.append([current, busy[0]])
        current = busy[1]
    if current < day_end:
        free_list.append([current, day_end])
    
    return free_list

def find_meeting_time(betty_free, scott_free, duration=30):
    common_free = []
    i = j = 0
    while i < len(betty_free) and j < len(scott_free):
        betty_int = betty_free[i]
        scott_int = scott_free[j]
        start = max(betty_int[0], scott_int[0])
        end = min(betty_int[1], scott_int[1])
        if start < end:
            common_free.append([start, end])
        if betty_int[1] < scott_int[1]:
            i += 1
        else:
            j += 1
    
    for interval in common_free:
        if interval[1] - interval[0] >= duration:
            return [interval[0], interval[0] + duration]
    return None

def main():
    betty_busy = {
        'Tuesday': ["9:00-9:30", "11:30-12:00", "12:30-13:00", "13:30-14:00", "16:30-17:00"],
        'Wednesday': ["9:30-10:30", "13:00-13:30", "14:00-14:30"],
        'Thursday': ["9:30-10:00", "11:30-12:00", "14:00-14:30", "15:00-15:30", "16:30-17:00"]
    }
    
    scott_busy = {
        'Tuesday': ["9:00-9:30", "10:00-11:00", "11:30-12:00", "12:30-13:30", "14:00-15:00", "16:00-16:30"],
        'Wednesday': ["9:30-12:30", "13:00-13:30", "14:00-14:30", "15:00-15:30", "16:00-16:30"],
        'Thursday': ["9:00-9:30", "10:00-10:30", "11:00-12:00", "12:30-13:00", "15:00-16:00", "16:30-17:00"]
    }
    
    days_order = ['Tuesday', 'Thursday', 'Wednesday']
    duration = 30
    day_start = 0
    day_end = 480
    
    for day in days_order:
        betty_intervals = betty_busy[day]
        scott_intervals = scott_busy[day]
        
        betty_free = get_free_intervals(betty_intervals, day_start, day_end)
        scott_free = get_free_intervals(scott_intervals, day_start, day_end)
        
        if day in ['Tuesday', 'Thursday']:
            betty_free_constrained = []
            for interval in betty_free:
                start = max(interval[0], 360)  # 15:00 in minutes
                end = interval[1]
                if start < end:
                    betty_free_constrained.append([start, end])
            betty_free = betty_free_constrained
        
        meeting_time = find_meeting_time(betty_free, scott_free, duration)
        if meeting_time:
            start_time_min = meeting_time[0]
            end_time_min = meeting_time[1]
            start_time_str = minutes_to_time(start_time_min)
            end_time_str = minutes_to_time(end_time_min)
            print(f"{day} {start_time_str}:{end_time_str}")
            return
    
    print("No meeting time found")

if __name__ == "__main__":
    main()