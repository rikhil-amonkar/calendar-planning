def min_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_available_intervals(work_start, work_end, blocked_intervals):
    blocked_sorted = sorted(blocked_intervals, key=lambda x: x[0])
    available = []
    current_start = work_start
    for start, end in blocked_sorted:
        if start > current_start:
            available.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < work_end:
        available.append((current_start, work_end))
    return available

martha_blocked = {
    'Monday': [(16*60, 17*60)],
    'Tuesday': [(15*60, 15*60 + 30)],
    'Wednesday': [(10*60, 11*60), (14*60, 14*60 + 30)]
}

beverly_blocked = {
    'Monday': [(9*60, 13*60 + 30), (14*60, 17*60)],
    'Tuesday': [(9*60, 17*60)],
    'Wednesday': [(9*60 + 30, 15*60 + 30), (16*60 + 30, 17*60)]
}

days = ['Monday', 'Tuesday', 'Wednesday']

for day in days:
    m_blocked = martha_blocked.get(day, [])
    b_blocked = beverly_blocked.get(day, [])
    m_available = get_available_intervals(9*60, 17*60, m_blocked)
    b_available = get_available_intervals(9*60, 17*60, b_blocked)
    for m_start, m_end in m_available:
        for b_start, b_end in b_available:
            overlap_start = max(m_start, b_start)
            overlap_end = min(m_end, b_end)
            if overlap_end > overlap_start:
                duration = overlap_end - overlap_start
                if duration >= 60:
                    start_time = min_to_time(overlap_start)
                    end_time = min_to_time(overlap_end)
                    start_hh, start_mm = start_time.split(':')
                    end_hh, end_mm = end_time.split(':')
                    time_str = f"{start_hh}:{start_mm}:{end_hh}:{end_mm}"
                    print(f"{time_str} {day}")
                    exit()