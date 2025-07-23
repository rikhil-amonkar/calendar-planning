def min_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = [sorted_intervals[0]]
    for current in sorted_intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def main():
    work_start = 9 * 60  # 540 minutes (9:00)
    work_end = 17 * 60   # 1020 minutes (17:00)
    duration = 60         # 60 minutes (1 hour)
    wednesday_pref = 12 * 60 + 30  # 750 minutes (12:30)

    # Define busy intervals in minutes (start, end) - half-open [start, end)
    diane_busy = {
        'Monday': [(12*60, 12*60+30), (15*60, 15*60+30)],
        'Tuesday': [(10*60, 11*60), (11*60+30, 12*60), (12*60+30, 13*60), (16*60, 17*60)],
        'Wednesday': [(9*60, 9*60+30), (14*60+30, 15*60), (16*60+30, 17*60)],
        'Thursday': [(15*60+30, 16*60+30)],
        'Friday': [(9*60+30, 11*60+30), (14*60+30, 15*60), (16*60, 17*60)]
    }
    
    matthew_busy = {
        'Monday': [(9*60, 10*60), (10*60+30, 17*60)],
        'Tuesday': [(9*60, 17*60)],
        'Wednesday': [(9*60, 11*60), (12*60, 14*60+30), (16*60, 17*60)],
        'Thursday': [(9*60, 16*60)],
        'Friday': [(9*60, 17*60)]
    }
    
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    
    for day in days:
        all_busy = diane_busy.get(day, []) + matthew_busy.get(day, [])
        if not all_busy:
            free_intervals = [(work_start, work_end)]
        else:
            merged_busy = merge_intervals(all_busy)
            free_intervals = []
            current = work_start
            for start, end in merged_busy:
                if current < start:
                    free_intervals.append((current, start))
                current = max(current, end)
            if current < work_end:
                free_intervals.append((current, work_end))
        
        for start_min, end_min in free_intervals:
            if end_min - start_min >= duration:
                if day == 'Wednesday':
                    if start_min < wednesday_pref:
                        continue
                meeting_start = start_min
                meeting_end = meeting_start + duration
                start_str = min_to_time(meeting_start)
                end_str = min_to_time(meeting_end)
                print(day)
                print(f"{start_str.replace(':', '')[:2]}:{start_str.replace(':', '')[2:]}:{end_str.replace(':', '')[:2]}:{end_str.replace(':', '')[2:]}")
                return
    
    print("No suitable time found")

if __name__ == "__main__":
    main()