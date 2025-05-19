def parse_time(s):
    hours, minutes = map(int, s.split(':'))
    return hours * 60 + minutes

def format_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def get_free_slots(busy_intervals, start, end):
    free = []
    prev_end = start
    for start_busy, end_busy in sorted(busy_intervals):
        if start_busy > prev_end:
            free.append((prev_end, start_busy))
        prev_end = max(prev_end, end_busy)
    if prev_end < end:
        free.append((prev_end, end))
    return free

def find_meeting_slot():
    work_start = parse_time("09:00")
    work_end = parse_time("17:00")
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    
    megan_busy = {
        'Monday': [(parse_time("13:00"), parse_time("13:30")), (parse_time("14:00"), parse_time("15:30"))],
        'Tuesday': [(parse_time("09:00"), parse_time("09:30")), (parse_time("12:00"), parse_time("12:30")), (parse_time("16:00"), parse_time("17:00"))],
        'Wednesday': [(parse_time("09:30"), parse_time("10:00")), (parse_time("10:30"), parse_time("11:30")), (parse_time("12:30"), parse_time("14:00")), (parse_time("16:00"), parse_time("16:30"))],
        'Thursday': [(parse_time("13:30"), parse_time("14:30")), (parse_time("15:00"), parse_time("15:30"))]
    }
    
    daniel_busy = {
        'Monday': [(parse_time("10:00"), parse_time("11:30")), (parse_time("12:30"), parse_time("15:00"))],
        'Tuesday': [(parse_time("09:00"), parse_time("10:00")), (parse_time("10:30"), parse_time("17:00"))],
        'Wednesday': [(parse_time("09:00"), parse_time("10:00")), (parse_time("10:30"), parse_time("11:30")), (parse_time("12:00"), parse_time("17:00"))],
        'Thursday': [(parse_time("09:00"), parse_time("12:00")), (parse_time("12:30"), parse_time("14:30")), (parse_time("15:00"), parse_time("15:30")), (parse_time("16:00"), parse_time("17:00"))]
    }
    
    for day in days:
        megan_slots = get_free_slots(megan_busy.get(day, []), work_start, work_end)
        daniel_slots = get_free_slots(daniel_busy.get(day, []), work_start, work_end)
        
        i = j = 0
        while i < len(megan_slots) and j < len(daniel_slots):
            m_start, m_end = megan_slots[i]
            d_start, d_end = daniel_slots[j]
            
            overlap_start = max(m_start, d_start)
            overlap_end = min(m_end, d_end)
            
            if overlap_start < overlap_end:
                if overlap_end - overlap_start >= 60:
                    start = overlap_start
                    return f"{day} {format_time(start)}:{format_time(start + 60)}"
                if overlap_end == m_end:
                    i += 1
                else:
                    j += 1
            else:
                if m_end <= d_end:
                    i += 1
                else:
                    j += 1
    
    return "No slot found"

result = find_meeting_slot()
day, time = result.split()
start, end = time.split(':')
print(f"{day} {start}:{end}")