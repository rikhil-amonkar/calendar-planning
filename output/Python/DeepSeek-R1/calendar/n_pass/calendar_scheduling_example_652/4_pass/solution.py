def calculate_free_intervals(start_bound, end_bound, busy_intervals):
    busy_intervals = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current = start_bound
    for b_start, b_end in busy_intervals:
        if b_start > end_bound:
            break
        if current < b_start:
            free.append((current, b_start))
        current = max(current, b_end)
        if current >= end_bound:
            break
    if current < end_bound:
        free.append((current, end_bound))
    return free

def find_overlapping_intervals(intervals1, intervals2):
    overlapping = []
    for start1, end1 in intervals1:
        for start2, end2 in intervals2:
            low = max(start1, start2)
            high = min(end1, end2)
            if low < high:
                overlapping.append((low, high))
    overlapping.sort(key=lambda x: x[0])
    return overlapping

def main():
    meeting_duration = 30
    work_start = 9 * 60
    work_end = 17 * 60
    
    # Skip Monday due to unavailable time slot constraint
    days = ['Tuesday', 'Wednesday', 'Thursday', 'Friday']
    
    jesse_busy = {
        'Monday': [],
        'Tuesday': [(540, 570), (780, 810), (840, 900)],
        'Wednesday': [(540, 660), (720, 840)],
        'Thursday': [(540, 720), (750, 960)],
        'Friday': [(540, 600), (840, 900)]
    }
    
    lawrence_busy = {
        'Monday': [(13*60, 17*60)],
        'Tuesday': [(570, 630), (690, 750), (780, 810), (870, 900), (930, 990)],
        'Wednesday': [],
        'Thursday': [],
        'Friday': []
    }
    
    lawrence_end_time = {
        'Monday': 13 * 60,
        'Tuesday': 16 * 60 + 30,
        'Wednesday': 16 * 60,
        'Thursday': 12 * 60,
        'Friday': 14 * 60
    }
    
    for day in days:
        jesse_busy_list = jesse_busy[day]
        lawrence_busy_list = lawrence_busy[day]
        lawrence_end_bound = lawrence_end_time[day]
        
        jesse_free = calculate_free_intervals(work_start, work_end, jesse_busy_list)
        lawrence_free = calculate_free_intervals(work_start, lawrence_end_bound, lawrence_busy_list)
        
        overlapping = find_overlapping_intervals(jesse_free, lawrence_free)
        
        meeting_start = None
        for start, end in overlapping:
            if end - start >= meeting_duration:
                meeting_start = start
                break
        
        if meeting_start is not None:
            meeting_end = meeting_start + meeting_duration
            start_hour = meeting_start // 60
            start_min = meeting_start % 60
            end_hour = meeting_end // 60
            end_min = meeting_end % 60
            # Format with leading zeros for single-digit hours/minutes
            time_str = f"{{{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}}}"
            print(day)
            print(time_str)
            return
    
    print("No suitable time found")

if __name__ == "__main__":
    main()