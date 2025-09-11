blocked_times = {
    'Doris': [(540, 660), (810, 840), (960, 990)],
    'Theresa': [(600, 720)],
    'Christian': [],
    'Terry': [(570, 600), (690, 720), (750, 780), (810, 840), (870, 900), (930, 1020)],
    'Carolyn': [(540, 630), (660, 690), (720, 780), (810, 870), (900, 1020)],
    'Kyle': [(540, 570), (690, 720), (750, 780), (870, 1020)]
}

def to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

for start in range(540, 990 + 1):
    slot_end = start + 30
    valid = True
    for person in blocked_times:
        for (b_start, b_end) in blocked_times[person]:
            if start < b_end and b_start < slot_end:
                valid = False
                break
        if not valid:
            break
    if valid:
        start_time = to_time(start)
        end_time = to_time(slot_end)
        print(f"{{{start_time}:{end_time}}} Monday")
        break