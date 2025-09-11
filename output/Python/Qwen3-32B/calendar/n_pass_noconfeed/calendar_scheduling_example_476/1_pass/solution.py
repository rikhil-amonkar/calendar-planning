participants = {
    'Daniel': [],
    'Kathleen': [(870, 930)],
    'Carolyn': [(720, 750), (780, 810)],
    'Roger': [],
    'Cheryl': [(540, 570), (600, 690), (750, 810), (840, 1020)],
    'Virginia': [(570, 690), (720, 750), (780, 810), (870, 930), (960, 1020)],
    'Angela': [(570, 600), (630, 690), (720, 750), (780, 810), (840, 990)]
}

def is_slot_free(slot_start, slot_end, busy_times):
    for b_start, b_end in busy_times:
        if slot_start < b_end and slot_end > b_start:
            return False
    return True

for start in range(540, 991, 30):
    if start < 750:  # Roger's preference
        continue
    slot_end = start + 30
    valid = True
    for _, busy in participants.items():
        if not is_slot_free(start, slot_end, busy):
            valid = False
            break
    if valid:
        start_h = start // 60
        start_m = start % 60
        end_h = slot_end // 60
        end_m = slot_end % 60
        start_time = f"{start_h:02d}:{start_m:02d}"
        end_time = f"{end_h:02d}:{end_m:02d}"
        print(f"{start_time}:{end_time} Monday")
        break