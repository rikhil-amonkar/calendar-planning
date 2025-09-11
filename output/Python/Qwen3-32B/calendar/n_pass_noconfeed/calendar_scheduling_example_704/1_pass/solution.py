def time_to_minutes(t_str):
    h, m = map(int, t_str.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def generate_available_blocks(busy_times, work_start, work_end):
    busy = []
    for s, e in busy_times:
        start = time_to_minutes(s)
        end = time_to_minutes(e)
        busy.append((start, end))
    busy.sort()
    available_blocks = []
    previous_end = work_start
    for start, end in busy:
        if previous_end < start:
            duration = start - previous_end
            if duration >= 30:
                available_blocks.append((previous_end, start))
        previous_end = end
    if previous_end < work_end:
        duration = work_end - previous_end
        if duration >= 30:
            available_blocks.append((previous_end, work_end))
    return available_blocks

busy_mon = [
    ('10:30', '11:00'),
    ('12:00', '12:30'),
    ('13:00', '15:00'),
    ('15:30', '16:30'),
]

busy_tue = [
    ('09:00', '12:00'),
    ('14:00', '15:30'),
    ('16:30', '17:00'),
]

busy_wed = [
    ('10:30', '11:00'),
    ('11:30', '12:00'),
    ('12:30', '13:00'),
    ('14:00', '14:30'),
    ('15:00', '16:00'),
]

days_order = ['Monday', 'Tuesday', 'Wednesday']
busy_dict = {
    'Monday': busy_mon,
    'Tuesday': busy_tue,
    'Wednesday': busy_wed
}

work_start = 9 * 60  # 540
work_end = 17 * 60   # 1020

for day in days_order:
    busy_times = busy_dict[day]
    available_blocks = generate_available_blocks(busy_times, work_start, work_end)
    if available_blocks:
        earliest_block_start = available_blocks[0][0]
        start_time = minutes_to_time(earliest_block_start)
        end_time = minutes_to_time(earliest_block_start + 30)
        print(f"{day} {start_time}:{end_time}")
        break