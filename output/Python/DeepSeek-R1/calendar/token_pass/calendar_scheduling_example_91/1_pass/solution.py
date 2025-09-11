def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return (hours - 9) * 60 + minutes

def minutes_to_time(minutes):
    hours = 9 + minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def parse_busy_intervals(busy_list):
    intervals = []
    for busytime in busy_list:
        start_str, end_str = busytime.split('-')
        start_min = time_to_minutes(start_str)
        end_min = time_to_minutes(end_str)
        intervals.append((start_min, end_min))
    return intervals

def find_free_intervals(busy_intervals, start=0, end=480):
    busy_intervals.sort(key=lambda x: x[0])
    free_intervals = []
    current = start
    for busystart, busyend in busy_intervals:
        if current < busystart:
            free_intervals.append((current, busystart))
        current = busyend
    if current < end:
        free_intervals.append((current, end))
    return free_intervals

def intersect_intervals(intervals1, intervals2):
    common = []
    for start1, end1 in intervals1:
        for start2, end2 in intervals2:
            low = max(start1, start2)
            high = min(end1, end2)
            if low < high:
                common.append((low, high))
    return common

def main():
    danielle_busy = ["9:00-10:00", "10:30-11:00", "14:30-15:00", "15:30-16:00", "16:30-17:00"]
    bruce_busy = ["11:00-11:30", "12:30-13:00", "14:00-14:30", "15:30-16:00"]
    eric_busy = ["9:00-9:30", "10:00-11:00", "11:30-13:00", "14:30-15:30"]
    
    danielle_intervals = parse_busy_intervals(danielle_busy)
    bruce_intervals = parse_busy_intervals(bruce_busy)
    eric_intervals = parse_busy_intervals(eric_busy)
    
    danielle_free = find_free_intervals(danielle_intervals)
    bruce_free = find_free_intervals(bruce_intervals)
    eric_free = find_free_intervals(eric_intervals)
    
    common_d_b = intersect_intervals(danielle_free, bruce_free)
    common_all = intersect_intervals(common_d_b, eric_free)
    
    meeting_duration = 60
    meeting_start = None
    for start, end in common_all:
        if end - start >= meeting_duration:
            meeting_start = start
            break
            
    if meeting_start is not None:
        start_time_str = minutes_to_time(meeting_start)
        end_time_str = minutes_to_time(meeting_start + meeting_duration)
        print(f"{start_time_str}:{end_time_str}")
        print("Monday")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()