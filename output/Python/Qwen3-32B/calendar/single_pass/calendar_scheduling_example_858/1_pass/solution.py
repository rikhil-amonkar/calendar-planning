def to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

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

def get_free_intervals(busy_intervals):
    merged = merge_intervals(busy_intervals)
    free = []
    prev_end = to_minutes('9:00')  # 540
    for start, end in merged:
        if prev_end < start:
            free.append( (prev_end, start) )
        prev_end = end
    if prev_end < to_minutes('17:00'):  # 1020
        free.append( (prev_end, to_minutes('17:00')) )
    return free

def find_overlap(carl, margaret):
    start = max(carl[0], margaret[0])
    end = min(carl[1], margaret[1])
    if start < end:
        return (start, end)
    else:
        return None

def to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

carl_busy = {
    'Monday': [(to_minutes('11:00'), to_minutes('11:30'))],
    'Tuesday': [(to_minutes('14:30'), to_minutes('15:00'))],
    'Wednesday': [(to_minutes('10:00'), to_minutes('11:30')), (to_minutes('13:00'), to_minutes('13:30'))],
    'Thursday': [(to_minutes('13:30'), to_minutes('14:00')), (to_minutes('16:00'), to_minutes('16:30'))],
}

margaret_busy = {
    'Monday': [(to_minutes('9:00'), to_minutes('10:30')), (to_minutes('11:00'), to_minutes('17:00'))],
    'Tuesday': [(to_minutes('9:30'), to_minutes('12:00')), (to_minutes('13:30'), to_minutes('14:00')), (to_minutes('15:30'), to_minutes('17:00'))],
    'Wednesday': [(to_minutes('9:30'), to_minutes('12:00')), (to_minutes('12:30'), to_minutes('13:00')), (to_minutes('13:30'), to_minutes('14:30')), (to_minutes('15:00'), to_minutes('17:00'))],
    'Thursday': [(to_minutes('10:00'), to_minutes('12:00')), (to_minutes('12:30'), to_minutes('14:00')), (to_minutes('14:30'), to_minutes('17:00'))],
}

valid_slots = []

days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

for day in days:
    carl_b = carl_busy.get(day, [])
    margaret_b = margaret_busy.get(day, [])
    
    carl_free = get_free_intervals(carl_b)
    margaret_free = get_free_intervals(margaret_b)
    
    for c_start, c_end in carl_free:
        for m_start, m_end in margaret_free:
            overlap = find_overlap( (c_start, c_end), (m_start, m_end) )
            if overlap:
                overlap_start, overlap_end = overlap
                duration = overlap_end - overlap_start
                if duration >= 60:
                    valid_slots.append( (day, overlap_start, overlap_start + 60) )

non_thursday_slots = [slot for slot in valid_slots if slot[0] != 'Thursday']

if non_thursday_slots:
    def sort_key(slot):
        day_order = {'Monday':0, 'Tuesday':1, 'Wednesday':2}
        return (day_order[slot[0]], slot[1])
    non_thursday_slots.sort(key=sort_key)
    earliest = non_thursday_slots[0]
else:
    valid_slots.sort(key=lambda slot: slot[1])
    earliest = valid_slots[0]

day = earliest[0]
start = earliest[1]
end = earliest[2]

start_time = to_time_str(start)
end_time = to_time_str(end)

print(f"{start_time}:{end_time} {day}")