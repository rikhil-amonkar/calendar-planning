def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

participants_busy = {
    'Jack': [(540, 570), (840, 870)],
    'Madison': [(570, 630), (780, 840), (900, 930), (990, 1020)],
    'Rachel': [(570, 630), (660, 690), (720, 810), (870, 930), (960, 1020)],
    'Douglas': [(540, 690), (720, 990)],
    'Ryan': [(540, 570), (780, 840), (870, 1020)],
}

for start in range(540, 991):
    window_end = start + 30
    valid = True
    for busy_list in participants_busy.values():
        for busy_start, busy_end in busy_list:
            if start < busy_end and busy_start < window_end:
                valid = False
                break
        if not valid:
            break
    if valid:
        start_time = minutes_to_time(start)
        end_time = minutes_to_time(window_end)
        print(f"{{{start_time}:{end_time}}} Monday")
        break