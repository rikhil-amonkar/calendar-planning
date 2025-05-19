def find_time():
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    duration = 30

    # Busy times for Adam and Roy in minutes
    adam_busy = [(9*60+30, 10*60), (12*60+30, 13*60), (14*60+30, 15*60), (16*60+30, 17*60)]
    roy_busy = [(10*60, 11*60), (11*60+30, 13*60), (13*60+30, 14*60+30), (16*60+30, 17*60)]

    # Combine and sort all busy intervals
    merged = sorted(adam_busy + roy_busy, key=lambda x: x[0])

    # Merge overlapping intervals
    merged_busy = []
    for start, end in merged:
        if not merged_busy:
            merged_busy.append([start, end])
        else:
            last_start, last_end = merged_busy[-1]
            if start <= last_end:
                merged_busy[-1][1] = max(last_end, end)
            else:
                merged_busy.append([start, end])

    # Check for available slot before first meeting
    if merged_busy[0][0] - work_start >= duration:
        return format_time(work_start, merged_busy[0][0], 'Monday')

    # Check gaps between meetings
    for i in range(1, len(merged_busy)):
        prev_end = merged_busy[i-1][1]
        curr_start = merged_busy[i][0]
        if curr_start - prev_end >= duration:
            return format_time(prev_end, curr_start, 'Monday')

    # Check after last meeting
    if work_end - merged_busy[-1][1] >= duration:
        return format_time(merged_busy[-1][1], work_end, 'Monday')

def format_time(start, end, day):
    start_hr, start_min = divmod(start, 60)
    end_hr, end_min = divmod(end, 60)
    return f"{day} {start_hr:02}:{start_min:02}:{end_hr:02}:{end_min:02}"

print(find_time())