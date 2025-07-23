def parse_time(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def min_to_hm(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return hour, minute

def merge_intervals(intervals):
    if not intervals:
        return []
    intervals_sorted = sorted(intervals, key=lambda x: x[0])
    merged = []
    start, end = intervals_sorted[0]
    for i in range(1, len(intervals_sorted)):
        if intervals_sorted[i][0] <= end:
            end = max(end, intervals_sorted[i][1])
        else:
            merged.append([start, end])
            start, end = intervals_sorted[i]
    merged.append([start, end])
    return merged

def compute_free_intervals(busy_intervals, day_start, day_end):
    if not busy_intervals:
        return [[day_start, day_end]]
    merged_busy = merge_intervals(busy_intervals)
    free = []
    if day_start < merged_busy[0][0]:
        free.append([day_start, merged_busy[0][0]])
    for i in range(len(merged_busy) - 1):
        free_start = merged_busy[i][1]
        free_end = merged_busy[i+1][0]
        if free_start < free_end:
            free.append([free_start, free_end])
    if merged_busy[-1][1] < day_end:
        free.append([merged_busy[-1][1], day_end])
    return free

def compute_common_free(free1, free2):
    i = j = 0
    common = []
    while i < len(free1) and j < len(free2):
        low = max(free1[i][0], free2[j][0])
        high = min(free1[i][1], free2[j][1])
        if low < high:
            common.append([low, high])
        if free1[i][1] < free2[j][1]:
            i += 1
        else:
            j += 1
    return common

def main():
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    work_start_min = 9 * 60
    work_end_min = 17 * 60

    megan_busy = {
        'Monday': [('13:00', '13:30'), ('14:00', '15:30')],
        'Tuesday': [('9:00', '9:30'), ('12:00', '12:30'), ('16:00', '17:00')],
        'Wednesday': [('9:30', '10:00'), ('10:30', '11:30'), ('12:30', '14:00'), ('16:00', '16:30')],
        'Thursday': [('13:30', '14:30'), ('15:00', '15:30')]
    }

    daniel_busy = {
        'Monday': [('10:00', '11:30'), ('12:30', '15:00')],
        'Tuesday': [('9:00', '10:00'), ('10:30', '17:00')],
        'Wednesday': [('9:00', '10:00'), ('10:30', '11:30'), ('12:00', '17:00')],
        'Thursday': [('9:00', '12:00'), ('12:30', '14:30'), ('15:00', '15:30'), ('16:00', '17:00')]
    }

    megan_busy_min = {}
    for day, intervals in megan_busy.items():
        megan_busy_min[day] = []
        for interval in intervals:
            start_min = parse_time(interval[0])
            end_min = parse_time(interval[1])
            megan_busy_min[day].append([start_min, end_min])

    daniel_busy_min = {}
    for day, intervals in daniel_busy.items():
        daniel_busy_min[day] = []
        for interval in intervals:
            start_min = parse_time(interval[0])
            end_min = parse_time(interval[1])
            daniel_busy_min[day].append([start_min, end_min])

    found = False
    meeting_day = None
    meeting_start_min = None

    for day in days:
        megan_busy_today = megan_busy_min.get(day, [])
        daniel_busy_today = daniel_busy_min.get(day, [])
        
        free_megan = compute_free_intervals(megan_busy_today, work_start_min, work_end_min)
        free_daniel = compute_free_intervals(daniel_busy_today, work_start_min, work_end_min)
        
        common_free = compute_common_free(free_megan, free_daniel)
        
        for interval in common_free:
            start, end = interval
            if end - start >= 60:
                meeting_start_min = start
                meeting_day = day
                found = True
                break
        if found:
            break

    if found:
        meeting_end_min = meeting_start_min + 60
        start_hour, start_minute = min_to_hm(meeting_start_min)
        end_hour, end_minute = min_to_hm(meeting_end_min)
        time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print(f"{meeting_day} {time_str}")
    else:
        print("No meeting time found")

if __name__ == "__main__":
    main()