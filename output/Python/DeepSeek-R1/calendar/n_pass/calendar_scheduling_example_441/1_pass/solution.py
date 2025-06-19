def compute_free_intervals(busy_intervals, work_start, work_end):
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

def intersect_two_intervals(intervals1, intervals2):
    if not intervals1 or not intervals2:
        return []
    i, j = 0, 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        low = max(start1, start2)
        high = min(end1, end2)
        if low < high:
            result.append((low, high))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

def main():
    work_start = 540
    work_end = 1020
    participants_busy = {
        "Joan": [(11*60+30, 12*60), (14*60+30, 15*60)],
        "Megan": [(9*60, 10*60), (14*60, 14*60+30), (16*60, 16*60+30)],
        "Austin": [],
        "Betty": [(9*60+30, 10*60), (11*60+30, 12*60), (13*60+30, 14*60), (16*60, 16*60+30)],
        "Judith": [(9*60, 11*60), (12*60, 13*60), (14*60, 15*60)],
        "Terry": [(9*60+30, 10*60), (11*60+30, 12*60+30), (13*60, 14*60), (15*60, 15*60+30), (16*60, 17*60)],
        "Kathryn": [(9*60+30, 10*60), (10*60+30, 11*60), (11*60+30, 13*60), (14*60, 16*60), (16*60+30, 17*60)]
    }
    
    all_free = []
    for busy_list in participants_busy.values():
        free_intervals = compute_free_intervals(busy_list, work_start, work_end)
        all_free.append(free_intervals)
    
    common = all_free[0]
    for i in range(1, len(all_free)):
        common = intersect_two_intervals(common, all_free[i])
    
    meeting_start = None
    for start, end in common:
        if end - start >= 30:
            meeting_start = start
            break
    
    if meeting_start is None:
        print("No suitable slot found")
    else:
        meeting_end = meeting_start + 30
        start_h = meeting_start // 60
        start_m = meeting_start % 60
        end_h = meeting_end // 60
        end_m = meeting_end % 60
        time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
        print("Monday")
        print(time_str)

if __name__ == "__main__":
    main()