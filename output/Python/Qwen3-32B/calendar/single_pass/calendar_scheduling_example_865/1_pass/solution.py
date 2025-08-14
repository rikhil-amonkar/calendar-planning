def minutes(h, m):
    return h * 60 + m

megan_busy = {
    'Monday': [(minutes(13, 0), minutes(13, 30)), (minutes(14, 0), minutes(15, 30))],
    'Tuesday': [(minutes(9, 0), minutes(9, 30)), (minutes(12, 0), minutes(12, 30)), (minutes(16, 0), minutes(17, 0))],
    'Wednesday': [(minutes(9, 30), minutes(10, 0)), (minutes(10, 30), minutes(11, 30)), (minutes(12, 30), minutes(14, 0)), (minutes(16, 0), minutes(16, 30))],
    'Thursday': [(minutes(13, 30), minutes(14, 30)), (minutes(15, 0), minutes(15, 30))],
}

daniel_busy = {
    'Monday': [(minutes(10, 0), minutes(11, 30)), (minutes(12, 30), minutes(15, 0))],
    'Tuesday': [(minutes(9, 0), minutes(10, 0)), (minutes(10, 30), minutes(17, 0))],
    'Wednesday': [(minutes(9, 0), minutes(10, 0)), (minutes(10, 30), minutes(11, 30)), (minutes(12, 0), minutes(17, 0))],
    'Thursday': [(minutes(9, 0), minutes(12, 0)), (minutes(12, 30), minutes(14, 30)), (minutes(15, 0), minutes(15, 30)), (minutes(16, 0), minutes(17, 0))],
}

def get_free_intervals(busy_intervals, start_work, end_work):
    free = []
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    prev_end = start_work
    for start, end in sorted_busy:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < end_work:
        free.append((prev_end, end_work))
    return free

def format_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

start_work = minutes(9, 0)
end_work = minutes(17, 0)

days_order = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

for day in days_order:
    meghan_intervals = meghan_busy.get(day, [])
    daniel_intervals = daniel_busy.get(day, [])
    
    meghan_free = get_free_intervals(meghan_intervals, start_work, end_work)
    daniel_free = get_free_intervals(daniel_intervals, start_work, end_work)
    
    for m_start, m_end in meghan_free:
        for d_start, d_end in daniel_free:
            overlap_start = max(m_start, d_start)
            overlap_end = min(m_end, d_end)
            if overlap_start < overlap_end:
                duration = overlap_end - overlap_start
                if duration >= 60:
                    start_str = format_time(overlap_start)
                    end_str = format_time(overlap_end)
                    print(f"{day} {start_str}:{end_str}")
                    exit()