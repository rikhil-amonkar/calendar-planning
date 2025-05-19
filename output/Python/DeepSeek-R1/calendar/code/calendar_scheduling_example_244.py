def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

participants = {
    "Walter": [],
    "Cynthia": [
        ("9:00", "9:30"),
        ("10:00", "10:30"),
        ("13:30", "14:30"),
        ("15:00", "16:00")
    ],
    "Ann": [
        ("10:00", "11:00"),
        ("13:00", "13:30"),
        ("14:00", "15:00"),
        ("16:00", "16:30")
    ],
    "Catherine": [
        ("9:00", "11:30"),
        ("12:30", "13:30"),
        ("14:30", "17:00")
    ],
    "Kyle": [
        ("9:00", "9:30"),
        ("10:00", "11:30"),
        ("12:00", "12:30"),
        ("13:00", "14:30"),
        ("15:00", "16:00")
    ]
}

# Convert all busy times to minutes
busy_slots = {}
for person, slots in participants.items():
    busy_slots[person] = []
    for start, end in slots:
        start_min = time_to_minutes(start)
        end_min = time_to_minutes(end)
        busy_slots[person].append((start_min, end_min))

# Check every possible 30-minute slot between 9:00 and 17:00
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60   # 17:00 in minutes

for slot_start in range(start_time, end_time - 30 + 1):
    slot_end = slot_start + 30
    valid = True
    for person, slots in busy_slots.items():
        for busy_start, busy_end in slots:
            if not (slot_end <= busy_start or slot_start >= busy_end):
                valid = False
                break
        if not valid:
            break
    if valid:
        proposed_start = minutes_to_time(slot_start)
        proposed_end = minutes_to_time(slot_end)
        print(f"Monday:{proposed_start}:{proposed_end}")
        exit()

# Fallback in case no slot found (though problem states there's a solution)
print("No valid slot found")