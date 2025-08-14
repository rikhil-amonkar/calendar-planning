participants = [
    [],  # Natalie
    [(690, 720), (870, 900)],  # David
    [(570, 600), (690, 720), (780, 810), (870, 900)],  # Douglas
    [(540, 570), (600, 660), (690, 750), (810, 900), (930, 960), (990, 1020)],  # Ralph
    [(540, 600), (720, 750), (780, 810), (870, 900), (930, 1020)]  # Jordan
]

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

for start in range(840, 990 + 1):  # 840 to 990 inclusive
    end = start + 30
    valid = True
    for busy_list in participants:
        for (b_start, b_end) in busy_list:
            if start < b_end and end > b_start:
                valid = False
                break
        if not valid:
            break
    if valid:
        time_str = f"{minutes_to_time(start)}:{minutes_to_time(end)}"
        print(f"{time_str} Monday")
        exit()