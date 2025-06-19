def get_free_intervals(busy_intervals, work_start, work_end):
    if not busy_intervals:
        return [[work_start, work_end]]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current = work_start
    for interval in sorted_busy:
        if current < interval[0]:
            free.append([current, interval[0]])
        current = max(current, interval[1])
    if current < work_end:
        free.append([current, work_end])
    return free

def get_overlapping_intervals(intervals1, intervals2):
    i = j = 0
    overlapping = []
    while i < len(intervals1) and j < len(intervals2):
        low = max(intervals1[i][0], intervals2[j][0])
        high = min(intervals1[i][1], intervals2[j][1])
        if low < high:
            overlapping.append([low, high])
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return overlapping

def main():
    work_start = 0
    work_end = 480
    
    eric_busy = [[180, 240], [300, 360]]
    henry_busy = [[30, 60], [90, 120], [150, 210], [240, 270], [330, 360], [420, 480]]
    
    eric_free = get_free_intervals(eric_busy, work_start, work_end)
    henry_free = get_free_intervals(henry_busy, work_start, work_end)
    
    overlapping = get_overlapping_intervals(eric_free, henry_free)
    
    meeting_start_min = None
    meeting_end_min = None
    for interval in overlapping:
        start, end = interval
        if end - start >= 30:
            meeting_start_min = start
            meeting_end_min = meeting_start_min + 30
            break
    
    start_hour = 9 + meeting_start_min // 60
    start_minute = meeting_start_min % 60
    end_hour = 9 + meeting_end_min // 60
    end_minute = meeting_end_min % 60
    
    time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
    
    print("Monday")
    print(time_str)

if __name__ == "__main__":
    main()