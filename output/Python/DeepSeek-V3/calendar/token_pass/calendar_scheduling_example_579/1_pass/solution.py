def time_to_min(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Work hours
work_start = time_to_min("9:00")
work_end = time_to_min("17:00")

# Christine's meetings
christine_meetings = [
    (time_to_min("11:00"), time_to_min("11:30")),
    (time_to_min("15:00"), time_to_min("15:30"))
]

# Helen's blocked times
helen_blocked = [
    (time_to_min("9:30"), time_to_min("10:30")),
    (time_to_min("11:00"), time_to_min("11:30")),
    (time_to_min("12:00"), time_to_min("12:30")),
    (time_to_min("13:30"), time_to_min("16:00")),
    (time_to_min("16:30"), time_to_min("17:00"))
]

# Helen cannot meet after 15:00
helen_end_availability = time_to_min("15:00")

# Generate free slots for Christine within work hours
def get_free_slots(busy_slots, start, end):
    free = []
    current = start
    for bs, be in sorted(busy_slots):
        if current < bs:
            free.append((current, bs))
        current = max(current, be)
    if current < end:
        free.append((current, end))
    return free

christine_free = get_free_slots(christine_meetings, work_start, work_end)
helen_free = get_free_slots(helen_blocked, work_start, work_end)

# Apply Helen's "cannot meet after 15:00" constraint
helen_free = [(s, min(e, helen_end_availability)) for s, e in helen_free if s < helen_end_availability]

# Find overlapping 30-minute slots
meeting_duration = 30
possible_slots = []

for c_start, c_end in christine_free:
    for h_start, h_end in helen_free:
        overlap_start = max(c_start, h_start)
        overlap_end = min(c_end, h_end)
        if overlap_end - overlap_start >= meeting_duration:
            possible_slots.append((overlap_start, overlap_end))

# Pick earliest slot
if possible_slots:
    # Sort by start time
    possible_slots.sort(key=lambda x: x[0])
    chosen_start = possible_slots[0][0]
    chosen_end = chosen_start + meeting_duration
    print(f"Monday {min_to_time(chosen_start)}:{min_to_time(chosen_end)}")
else:
    print("No slot found")