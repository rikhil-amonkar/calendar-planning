def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def time_to_str(start, end):
    return f"{minutes_to_time(start)}:{minutes_to_time(end)}"

def subtract_busy(full_start, full_end, busy_intervals):
    busy_intervals.sort()
    available = []
    current_start = full_start
    for start, end in busy_intervals:
        if current_start < start:
            available.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < full_end:
        available.append((current_start, full_end))
    return available

def find_meeting_time():
    diane_busy = {
        'Monday': [(720, 750), (900, 930)],
        'Tuesday': [(600, 660), (690, 720), (750, 780), (960, 1020)],
        'Wednesday': [(540, 570), (870, 900), (990, 1020)],
        'Thursday': [(930, 990)],
        'Friday': [(570, 690), (870, 900), (960, 1020)]
    }
    matthew_busy = {
        'Monday': [(540, 600), (630, 1020)],
        'Tuesday': [(540, 1020)],
        'Wednesday': [(540, 660), (720, 870), (960, 1020)],
        'Thursday': [(540, 960)],
        'Friday': [(540, 1020)]
    }
    full_start = 540  # 9:00 AM
    full_end = 1020   # 5:00 PM

    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    for day in days:
        diane_available = subtract_busy(full_start, full_end, diane_busy.get(day, []))
        matthew_available = subtract_busy(full_start, full_end, matthew_busy.get(day, []))
        overlaps = []
        for d_start, d_end in diane_available:
            for m_start, m_end in matthew_available:
                start = max(d_start, m_start)
                end = min(d_end, m_end)
                if start < end:
                    overlaps.append((start, end))
        for start, end in overlaps:
            if end - start >= 60:
                if day == 'Wednesday' and start < 750:
                    continue
                time_str = time_to_str(start, start + 60)
                print(f"{day} {time_str}")
                return

find_meeting_time()