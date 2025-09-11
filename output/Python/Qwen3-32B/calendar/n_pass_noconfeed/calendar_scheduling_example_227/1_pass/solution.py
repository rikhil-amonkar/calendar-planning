def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

participants = {
    'Natalie': [],
    'David': [(690, 720), (870, 900)],
    'Douglas': [(570, 600), (690, 720), (780, 810), (870, 900)],
    'Ralph': [(540, 570), (600, 660), (690, 750), (810, 900), (930, 960), (990, 1020)],
    'Jordan': [(540, 600), (720, 750), (780, 810), (870, 900), (930, 1020)]
}

def is_slot_free(slot_start, slot_end, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        if slot_start < busy_end and busy_start < slot_end:
            return False
    return True

for start in range(840, 990 + 1):
    end = start + 30
    all_free = True
    for busy_intervals in participants.values():
        if not is_slot_free(start, end, busy_intervals):
            all_free = False
            break
    if all_free:
        start_time = minutes_to_time(start)
        end_time = minutes_to_time(end)
        print(f"{start_time}:{end_time} Monday")
        break