def time_to_minutes(t):
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    prev_end = work_start
    for start, end in sorted_busy:
        if start > prev_end:
            free.append([prev_end, start])
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append([prev_end, work_end])
    return free

def find_meeting_time():
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("13:30")  # Helen's constraint
    duration = 30

    # Define busy intervals in minutes (within adjusted work hours)
    margaret_busy = [
        [time_to_minutes("09:00"), time_to_minutes("10:00")],
        [time_to_minutes("10:30"), time_to_minutes("11:00")],
        [time_to_minutes("11:30"), time_to_minutes("12:00")],
        [time_to_minutes("13:00"), time_to_minutes("13:30")]
    ]
    
    donna_busy = []  # No conflicts in adjusted window
    
    helen_busy = [
        [time_to_minutes("09:00"), time_to_minutes("09:30")],
        [time_to_minutes("10:00"), time_to_minutes("11:30")],
        [time_to_minutes("13:00"), time_to_minutes("13:30")]
    ]

    # Get free intervals
    margaret_free = get_free_intervals(margaret_busy, work_start, work_end)
    donna_free = get_free_intervals(donna_busy, work_start, work_end)
    helen_free = get_free_intervals(helen_busy, work_start, work_end)

    # Find common free intervals
    common_free = []
    for m_int in margaret_free:
        for h_int in helen_free:
            start = max(m_int[0], h_int[0])
            end = min(m_int[1], h_int[1])
            if start < end:
                common_free.append([start, end])
    
    final_free = []
    for c_int in common_free:
        for d_int in donna_free:
            start = max(c_int[0], d_int[0])
            end = min(c_int[1], d_int[1])
            if start < end:
                final_free.append([start, end])

    # Find first suitable slot
    for interval in final_free:
        available_start = interval[0]
        available_end = interval[1]
        if available_end - available_start >= duration:
            meeting_start = available_start
            meeting_end = meeting_start + duration
            return ("Monday", 
                    minutes_to_time(meeting_start),
                    minutes_to_time(meeting_end))

    return None

result = find_meeting_time()
if result:
    day, start, end = result
    print(f"{day} {start}:{end}")
else:
    print("No suitable time found")