def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"


def get_free_intervals(work_start, work_end, busy_intervals):
    busy_intervals.sort()
    free = []
    current_start = work_start
    for start, end in busy_intervals:
        if current_start < start:
            free.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < work_end:
        free.append((current_start, work_end))
    return free


def find_meeting_time(daniel_busy, bradley_busy):
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    for day in days:
        if day == 'Monday' or day == 'Friday':
            continue
        elif day == 'Tuesday':
            br_work_start = 12 * 60
            br_work_end = 17 * 60
        else:
            br_work_start = 9 * 60
            br_work_end = 17 * 60

        daniel_buses = daniel_busy.get(day, [])
        daniel_work_start = 9 * 60
        daniel_work_end = 17 * 60
        daniel_free = get_free_intervals(daniel_work_start, daniel_work_end, daniel_buses)

        br_buses = bradley_busy.get(day, [])
        adjusted_br_buses = []
        for start, end in br_buses:
            new_start = max(start, br_work_start)
            new_end = min(end, br_work_end)
            if new_start < new_end:
                adjusted_br_buses.append((new_start, new_end))
        br_free = get_free_intervals(br_work_start, br_work_end, adjusted_br_buses)

        def find_overlapping(intervals1, intervals2):
            i = j = 0
            result = []
            while i < len(intervals1) and j < len(intervals2):
                s1, e1 = intervals1[i]
                s2, e2 = intervals2[j]
                overlap_s = max(s1, s2)
                overlap_e = min(e1, e2)
                if overlap_s < overlap_e:
                    result.append((overlap_s, overlap_e))
                if e1 <= e2:
                    i += 1
                else:
                    j += 1
            return result

        overlapping = find_overlapping(daniel_free, br_free)

        for start, end in overlapping:
            if end - start >= 30:
                meeting_start = start
                meeting_end = meeting_start + 30
                return (day, meeting_start, meeting_end)
    return None


daniel_busy = {
    'Monday': [(570, 630), (720, 750), (780, 840), (870, 900), (930, 960)],
    'Tuesday': [(660, 720), (780, 810), (930, 960), (990, 1020)],
    'Wednesday': [(540, 600), (840, 870)],
    'Thursday': [(630, 660), (720, 780), (870, 900), (930, 960)],
    'Friday': [(540, 570), (690, 720), (780, 810), (1020, 1050)],
}

bradley_busy = {
    'Monday': [(570, 660), (690, 720), (750, 780), (840, 900)],
    'Tuesday': [(630, 660), (720, 780), (810, 840), (990, 1020)],
    'Wednesday': [(540, 600), (660, 780), (810, 840), (870, 1020)],
    'Thursday': [(540, 750), (810, 840), (870, 900), (930, 990)],
    'Friday': [(540, 570), (600, 750), (780, 810), (840, 870), (930, 990)],
}

result = find_meeting_time(daniel_busy, bradley_busy)
if result:
    day, start, end = result
    start_time = minutes_to_time(start)
    end_time = minutes_to_time(end)
    print(f"{start_time}:{end_time} {day}")
