def subtract_intervals(work, busy_list):
    free = [work]
    if not busy_list:
        return free
    busy_list = sorted(busy_list, key=lambda x: x[0])
    for busy in busy_list:
        new_free = []
        for interval in free:
            if busy[1] <= interval[0] or busy[0] >= interval[1]:
                new_free.append(interval)
            else:
                if interval[0] < busy[0]:
                    new_free.append((interval[0], busy[0]))
                if busy[1] < interval[1]:
                    new_free.append((busy[1], interval[1]))
        free = new_free
    return free

def intersect_intervals(list1, list2):
    common = []
    for a in list1:
        for b in list2:
            start = max(a[0], b[0])
            end = min(a[1], b[1])
            if start < end:
                common.append((start, end))
    return common

def main():
    work_start = 540  # 9:00 in minutes
    work_end = 1020   # 17:00 in minutes
    work_interval = (work_start, work_end)
    
    carl_busy = {
        'Monday': [(660, 690)],  # 11:00-11:30
        'Tuesday': [(870, 900)],  # 14:30-15:00
        'Wednesday': [(600, 690), (780, 810)],  # 10:00-11:30, 13:00-13:30
        'Thursday': [(810, 840), (960, 990)]   # 13:30-14:00, 16:00-16:30
    }
    
    margaret_busy = {
        'Monday': [(540, 630), (660, 1020)],  # 9:00-10:30, 11:00-17:00
        'Tuesday': [(570, 720), (810, 840), (930, 1020)],  # 9:30-12:00, 13:30-14:00, 15:30-17:00
        'Wednesday': [(570, 720), (750, 780), (810, 870), (900, 1020)],  # 9:30-12:00, 12:30-13:00, 13:30-14:30, 15:00-17:00
        'Thursday': [(600, 720), (750, 840), (870, 1020)]  # 10:00-12:00, 12:30-14:00, 14:30-17:00
    }
    
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    found = False
    result_day = None
    time_str = None
    
    for day in days:
        if found:
            break
        if day == 'Thursday' and not found:
            # Only consider Thursday if no other day found
            pass
        carl_busy_today = carl_busy.get(day, [])
        margaret_busy_today = margaret_busy.get(day, [])
        
        carl_free = subtract_intervals(work_interval, carl_busy_today)
        margaret_free = subtract_intervals(work_interval, margaret_busy_today)
        common_free = intersect_intervals(carl_free, margaret_free)
        
        for interval in common_free:
            if interval[1] - interval[0] >= 60:
                meeting_start = interval[0]
                meeting_end = meeting_start + 60
                start_hour = meeting_start // 60
                start_min = meeting_start % 60
                end_hour = meeting_end // 60
                end_min = meeting_end % 60
                time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
                result_day = day
                found = True
                break
    
    print(result_day)
    print(time_str)

if __name__ == "__main__":
    main()