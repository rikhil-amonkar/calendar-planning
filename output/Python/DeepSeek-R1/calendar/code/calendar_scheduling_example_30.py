def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def is_free(slot_start, slot_end, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        if not (slot_end <= busy_start or slot_start >= busy_end):
            return False
    return True

# Define work hours in minutes (9:00 to 17:00)
work_start = 9 * 60  # 540 minutes (9:00)
work_end = 17 * 60    # 1020 minutes (17:00)

# Define busy intervals for each participant in minutes
jeffrey_busy = [(9*60 + 30, 10*60), (10*60 + 30, 11*60)]
virginia_busy = [(9*60, 9*60 + 30), (10*60, 10*60 + 30),
                 (14*60 + 30, 15*60), (16*60, 16*60 + 30)]
melissa_busy = [(9*60, 11*60 + 30), (12*60, 12*60 + 30),
                (13*60, 15*60), (16*60, 17*60)]

# Generate all possible 30-minute slots within work hours
valid_slots = []
for start in range(work_start, work_end - 30 + 1, 30):
    end = start + 30
    if (is_free(start, end, jeffrey_busy) and
       is_free(start, end, virginia_busy) and
       is_free(start, end, melissa_busy):
        valid_slots.append(start)

# Split into preferred (before 14:00) and other slots
preferred_cutoff = 14 * 60  # 840 minutes (14:00)
preferred = [s for s in valid_slots if s + 30 <= preferred_cutoff]
other = [s for s in valid_slots if s not in preferred]

# Select best available slot
if preferred:
    best_slot = preferred[0]
elif other:
    best_slot = other[0]
else:
    best_slot = None

if best_slot is not None:
    start_time = minutes_to_time(best_slot)
    end_time = minutes_to_time(best_slot + 30)
    print(f"Monday:{start_time}:{end_time}")
else:
    print("No valid slot found")