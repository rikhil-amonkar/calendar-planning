def parse_time(s):
    hours, minutes = map(int, s.split(':'))
    return hours * 60 + minutes

def format_time(mins):
    return f"{mins // 60:02d}:{mins % 60:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = [sorted_intervals[0]]
    for current in sorted_intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def find_meeting_slot():
    work_start = parse_time("09:00")
    work_end = parse_time("17:00")
    days_order = ['Monday', 'Tuesday', 'Thursday', 'Friday', 'Wednesday']
    
    eugene_busy = {
        'Monday': [('11:00', '12:00'), ('13:30', '14:00'), ('14:30', '15:00'), ('16:00', '16:30')],
        'Wednesday': [('09:00', '09:30'), ('11:00', '11:30'), ('12:00', '12:30'), ('13:30', '15:00')],
        'Thursday': [('09:30', '10:00'), ('11:00', '12:30')],
        'Friday': [('10:30', '11:00'), ('12:00', '12:30'), ('13:00', '13:30')],
        'Tuesday': []
    }
    
    eric_busy = {
        'Monday': [('09:00', '17:00')],
        'Tuesday': [('09:00', '17:00')],
        'Wednesday': [('09:00', '11:30'), ('12:00', '14:00'), ('14:30', '16:30')],
        'Thursday': [('09:00', '17:00')],
        'Friday': [('09:00', '11:00'), ('11:30', '17:00')]
    }
    
    for day in days_order:
        eugene = [ (parse_time(s), parse_time(e)) for s, e in eugene_busy.get(day, []) ]
        eric = [ (parse_time(s), parse_time(e)) for s, e in eric_busy.get(day, []) ]
        combined = eugene + eric
        merged = merge_intervals(combined)
        
        available = []
        prev_end = work_start
        for start, end in merged:
            if start > prev_end:
                available.append( (prev_end, start) )
            prev_end = max(prev_end, end)
        if prev_end < work_end:
            available.append( (prev_end, work_end) )
        
        for slot in available:
            if slot[1] - slot[0] >= 30:
                start = slot[0]
                end_time = start + 30
                return (day, format_time(start), format_time(end_time))
    
    return None

result = find_meeting_slot()
if result:
    day, start, end = result
    print(f"{day} {start}:{end}")
else:
    print("No slot found")