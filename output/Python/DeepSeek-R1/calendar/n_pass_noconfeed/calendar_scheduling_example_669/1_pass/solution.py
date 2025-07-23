import itertools

def time_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    if not busy_intervals:
        return [(work_start, work_end)]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current = work_start
    for start, end in sorted_busy:
        if current < start:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def combine_intervals(intervals1, intervals2):
    combined = []
    for (s1, e1) in intervals1:
        for (s2, e2) in intervals2:
            low = max(s1, s2)
            high = min(e1, e2)
            if low < high:
                combined.append((low, high))
    return combined

def main():
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 30
    
    jean_busy = {
        'Tuesday': [
            (time_to_minutes("11:30"), time_to_minutes("12:00")),
            (time_to_minutes("16:00"), time_to_minutes("16:30"))
        ]
    }
    
    doris_busy = {
        'Monday': [
            (time_to_minutes("09:00"), time_to_minutes("11:30")),
            (time_to_minutes("12:00"), time_to_minutes("12:30")),
            (time_to_minutes("13:30"), time_to_minutes("16:00")),
            (time_to_minutes("16:30"), time_to_minutes("17:00"))
        ],
        'Tuesday': [
            (time_to_minutes("09:00"), time_to_minutes("17:00"))
        ]
    }
    
    days = ['Monday', 'Tuesday']
    candidate = None
    
    for day in days:
        jean_busy_today = jean_busy.get(day, [])
        jean_free = get_free_intervals(jean_busy_today, work_start, work_end)
        
        doris_busy_today = doris_busy.get(day, [])
        doris_free = get_free_intervals(doris_busy_today, work_start, work_end)
        
        common_free = combine_intervals(jean_free, doris_free)
        
        end_limit = work_end
        if day == 'Monday':
            end_limit = time_to_minutes("14:00")
        
        for start, end in common_free:
            slot_end = start + meeting_duration
            if slot_end <= min(end, end_limit):
                candidate = (day, start, slot_end)
                break
        if candidate:
            break
    
    if candidate:
        day, start_min, end_min = candidate
        start_time = minutes_to_time(start_min)
        end_time = minutes_to_time(end_min)
        print(f"{day} {start_time}:{end_time}")

if __name__ == "__main__":
    main()