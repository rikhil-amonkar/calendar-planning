def get_free_intervals(busy_list, start, end):
    if not busy_list:
        return [(start, end)]
    sorted_busy = sorted(busy_list, key=lambda x: x[0])
    free = []
    current = start
    for interval in sorted_busy:
        if current < interval[0]:
            free.append((current, interval[0]))
        current = max(current, interval[1])
    if current < end:
        free.append((current, end))
    return free

def intersect_intervals(intervals_a, intervals_b):
    i = j = 0
    res = []
    while i < len(intervals_a) and j < len(intervals_b):
        a_start, a_end = intervals_a[i]
        b_start, b_end = intervals_b[j]
        low = max(a_start, b_start)
        high = min(a_end, b_end)
        if low < high:
            res.append((low, high))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return res

def main():
    work_start = 540  # 9:00
    work_end = 1020   # 17:00
    russell_busy = {
        'Monday': [(630, 660)],   # 10:30-11:00
        'Tuesday': [(780, 810)]   # 13:00-13:30
    }
    alexander_busy = {
        'Monday': [(540, 690), (720, 870), (900, 1020)],
        'Tuesday': [(540, 600), (780, 840), (900, 930), (960, 990)]
    }
    days = ['Monday', 'Tuesday']
    found = False
    candidate_day = None
    start_meeting = None
    end_meeting = None

    for day in days:
        russell_list = russell_busy.get(day, [])
        alexander_list = alexander_busy.get(day, [])
        russell_free = get_free_intervals(russell_list, work_start, work_end)
        alexander_free = get_free_intervals(alexander_list, work_start, work_end)
        common = intersect_intervals(russell_free, alexander_free)
        
        for s, e in common:
            if day == 'Tuesday':
                s_adj = max(s, 810)  # 13:30 in minutes
            else:
                s_adj = s
            if e - s_adj >= 60:
                start_meeting = s_adj
                end_meeting = s_adj + 60
                candidate_day = day
                found = True
                break
        if found:
            break

    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h}:{m:02d}"

    start_str = format_time(start_meeting)
    end_str = format_time(end_meeting)
    time_str = f"{start_str}:{end_str}"

    print(candidate_day)
    print(time_str)

if __name__ == "__main__":
    main()