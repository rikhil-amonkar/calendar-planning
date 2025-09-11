participants = {
    'Gregory': [(540, 570), (690, 720)],
    'Jonathan': [(540, 570), (720, 750), (780, 810), (900, 960), (990, 1020)],
    'Barbara': [(600, 630), (810, 840)],
    'Jesse': [(600, 660), (750, 870)],
    'Alan': [(570, 660), (690, 750), (780, 930), (960, 1020)],
    'Nicole': [(540, 630), (690, 720), (750, 810), (840, 1020)],
    'Catherine': [(540, 630), (720, 810), (900, 930), (960, 990)]
}

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

for start in range(540, 990 + 1):
    valid = True
    for busy_list in participants.values():
        for b_start, b_end in busy_list:
            if start < b_end and b_start < start + 30:
                valid = False
                break
        if not valid:
            break
    if valid:
        start_time = minutes_to_time(start)
        end_time = minutes_to_time(start + 30)
        day = "Monday"
        print(f"{{{start_time}:{end_time}}} {day}")
        exit()