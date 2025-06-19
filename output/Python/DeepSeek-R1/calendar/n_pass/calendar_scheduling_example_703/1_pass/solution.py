def get_free_intervals(busy_intervals, work_start, work_end):
    if not busy_intervals:
        return [(work_start, work_end)]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current = work_start
    for interval in sorted_busy:
        if current < interval[0]:
            free.append((current, interval[0]))
        current = max(current, interval[1])
    if current < work_end:
        free.append((current, work_end))
    return free

def get_common_intervals(free1, free2):
    common = []
    for start1, end1 in free1:
        for start2, end2 in free2:
            low = max(start1, start2)
            high = min(end1, end2)
            if low < high:
                common.append((low, high))
    return common

def main():
    # Define work hours in minutes (9:00 to 17:00)
    work_start = 9 * 60  # 540 minutes
    work_end = 17 * 60   # 1020 minutes
    
    # Define busy intervals in minutes for each participant per day
    stephanie_busy = {
        'Monday': [(9*60+30, 10*60), (10*60+30, 11*60), (11*60+30, 12*60), (14*60, 14*60+30)],
        'Tuesday': [(12*60, 13*60)],
        'Wednesday': [(9*60, 10*60), (13*60, 14*60)]
    }
    
    betty_busy = {
        'Monday': [(9*60, 10*60), (11*60, 11*60+30), (14*60+30, 15*60), (15*60+30, 16*60)],
        'Tuesday': [(9*60, 9*60+30), (11*60+30, 12*60), (12*60+30, 14*60+30), (15*60+30, 16*60)],
        'Wednesday': [(10*60, 11*60+30), (12*60, 14*60), (14*60+30, 17*60)]
    }
    
    # Days in order of preference: Tuesday, Wednesday, Monday
    days = ['Tuesday', 'Wednesday', 'Monday']
    meeting_duration = 60  # minutes
    
    # Store the result
    result_day = None
    result_start = None
    
    for day in days:
        # Adjust work_end for Betty on Tuesday (cannot meet after 12:30)
        betty_work_end = 12*60 + 30 if day == 'Tuesday' else work_end
        stephanie_work_end = work_end
        
        # Get free intervals for Stephanie and Betty
        steph_free = get_free_intervals(stephanie_busy.get(day, []), work_start, stephanie_work_end)
        betty_free = get_free_intervals(betty_busy.get(day, []), work_start, betty_work_end)
        
        # Find common free intervals
        common_free = get_common_intervals(steph_free, betty_free)
        
        # Check for a slot of at least meeting_duration
        for start, end in common_free:
            if end - start >= meeting_duration:
                result_day = day
                result_start = start
                break
        if result_day is not None:
            break
    
    # Format the result
    start_hour = result_start // 60
    start_minute = result_start % 60
    end_time = result_start + meeting_duration
    end_hour = end_time // 60
    end_minute = end_time % 60
    
    time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
    print(f"{result_day} {time_str}")

if __name__ == "__main__":
    main()