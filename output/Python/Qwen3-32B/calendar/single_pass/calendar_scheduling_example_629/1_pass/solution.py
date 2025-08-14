def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_available_slots(blocked, start_work, end_work):
    blocked = sorted(blocked, key=lambda x: x[0])
    available = []
    prev_end = start_work
    for start, end in blocked:
        if prev_end < start:
            available.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < end_work:
        available.append((prev_end, end_work))
    return available

# Work hours on Tuesday: 9:00 (540) to 17:00 (1020)
start_work = 9 * 60
end_work = 17 * 60

# Margaret's blocked times on Tuesday
margaret_blocked = [(12 * 60, 12 * 60 + 30)]  # 12:00-12:30
# Generate available slots
margaret_available = get_available_slots(margaret_blocked, start_work, end_work)

# Apply Margaret's constraints: after 14:30 (14*60 +30 = 870)
margaret_filtered = []
for s, e in margaret_available:
    new_s = max(s, 14 * 60 + 30)  # 870
    new_e = min(e, end_work)
    if new_s < new_e:
        margaret_filtered.append((new_s, new_e))

# Alexis's blocked times on Tuesday
alexis_blocked = [
    (9 * 60, 9 * 60 + 30),        # 9:00-9:30
    (10 * 60, 10 * 60 + 30),      # 10:00-10:30
    (14 * 60, 16 * 60 + 30)       # 14:00-16:30
]
alexis_available = get_available_slots(alexis_blocked, start_work, end_work)

# Find overlapping slots
for s_m, e_m in margaret_filtered:
    for s_a, e_a in alexis_available:
        overlap_s = max(s_m, s_a)
        overlap_e = min(e_m, e_a)
        if overlap_s < overlap_e:
            duration = overlap_e - overlap_s
            if duration >= 30:
                # Found a valid slot
                start_time = time_to_str(overlap_s)
                end_time = time_to_str(overlap_e)
                print(f"Tuesday {start_time}:{end_time}")
                exit()