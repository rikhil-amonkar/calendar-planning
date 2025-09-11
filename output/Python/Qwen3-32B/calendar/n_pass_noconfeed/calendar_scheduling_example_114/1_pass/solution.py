def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

participants = {
    'Stephanie': [(600, 630), (960, 990)],
    'Cheryl': [(600, 630), (690, 720), (810, 840), (990, 1020)],
    'Bradley': [(570, 600), (630, 690), (810, 840), (870, 900), (930, 1020)],
    'Steven': [(540, 720), (780, 810), (870, 1020)]
}

for start in range(540, 961):  # 9:00 to 16:00 in minutes (end at 16:00 to allow 1hr meeting)
    end = start + 60
    conflict = False
    for busy_list in participants.values():
        for b_start, b_end in busy_list:
            if start < b_end and b_start < end:
                conflict = True
                break
        if conflict:
            break
    if not conflict:
        start_time = minutes_to_time(start)
        end_time = minutes_to_time(end)
        print(f"{start_time}:{end_time} Monday")
        break