def parse_time(s):
    hours, minutes = map(int, s.split(':'))
    return hours * 60 + minutes

def format_time(m):
    return f"{m // 60:02}:{m % 60:02}"

daniel_busy = {
    'Tuesday': [(parse_time('11:00'), parse_time('12:00')), (parse_time('13:00'), parse_time('13:30')),
                (parse_time('15:30'), parse_time('16:00')), (parse_time('16:30'), parse_time('17:00'))],
    'Thursday': [(parse_time('10:30'), parse_time('11:00')), (parse_time('12:00'), parse_time('13:00')),
                 (parse_time('14:30'), parse_time('15:00')), (parse_time('15:30'), parse_time('16:00'))]
}

bradley_busy = {
    'Tuesday': [(parse_time('12:00'), parse_time('13:00')), (parse_time('13:30'), parse_time('14:00')),
                (parse_time('15:30'), parse_time('16:30'))],
    'Thursday': [(parse_time('09:00'), parse_time('12:30')), (parse_time('13:30'), parse_time('14:00')),
                 (parse_time('14:30'), parse_time('15:00')), (parse_time('15:30'), parse_time('16:30'))]
}

work_start = parse_time('09:00')
work_end = parse_time('17:00')

def find_slot(day):
    merged = []
    for start, end in daniel_busy.get(day, []) + bradley_busy.get(day, []):
        merged.append((start, end))
    merged.sort()
    if not merged:
        return (work_start, work_start + 30)
    merged_combined = []
    for interval in merged:
        if not merged_combined:
            merged_combined.append(interval)
        else:
            last = merged_combined[-1]
            if interval[0] <= last[1]:
                merged_combined[-1] = (last[0], max(last[1], interval[1]))
            else:
                merged_combined.append(interval)
    free_slots = []
    prev_end = work_start
    for start, end in merged_combined:
        if start > prev_end:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_slots.append((prev_end, work_end))
    for start, end in free_slots:
        if end - start >= 30:
            return (start, start + 30)
    return None

# Check possible days considering preferences
for day in ['Tuesday', 'Thursday']:
    if day == 'Tuesday':
        slot = find_slot('Tuesday')
        if slot and slot[0] >= parse_time('12:00'):
            start, end = slot
            print(f"{day}:{format_time(start)}:{format_time(end)}")
            exit()
    elif day == 'Thursday':
        slot = find_slot('Thursday')
        if slot:
            start, end = slot
            print(f"{day}:{format_time(start)}:{format_time(end)}")
            exit()