from datetime import datetime, timedelta

# Define the day and time constraints
day_of_week = "Monday"
start_time_str = "09:00"
end_time_str = "17:00"
meeting_duration = 30  # in minutes

# Convert time strings to datetime objects for easier manipulation
def parse_time(time_str):
    return datetime.strptime(f"2023-01-01 {time_str}", "%Y-%m-%d %H:%M")

start_time = parse_time(start_time_str)
end_time = parse_time(end_time_str)

# Define busy intervals for each participant as (start, end) tuples
busy_intervals = {
    "Joan": [
        (parse_time("11:30"), parse_time("12:00")),
        (parse_time("14:30"), parse_time("15:00"))
    ],
    "Megan": [
        (parse_time("09:00"), parse_time("10:00")),
        (parse_time("14:00"), parse_time("14:30")),
        (parse_time("16:00"), parse_time("16:30"))
    ],
    "Austin": [],  # Free all day
    "Betty": [
        (parse_time("09:30"), parse_time("10:00")),
        (parse_time("11:30"), parse_time("12:00")),
        (parse_time("13:30"), parse_time("14:00")),
        (parse_time("16:00"), parse_time("16:30"))
    ],
    "Judith": [
        (parse_time("09:00"), parse_time("11:00")),
        (parse_time("12:00"), parse_time("13:00")),
        (parse_time("14:00"), parse_time("15:00"))
    ],
    "Terry": [
        (parse_time("09:30"), parse_time("10:00")),
        (parse_time("11:30"), parse_time("12:30")),
        (parse_time("13:00"), parse_time("14:00")),
        (parse_time("15:00"), parse_time("15:30")),
        (parse_time("16:00"), parse_time("17:00"))
    ],
    "Kathryn": [
        (parse_time("09:30"), parse_time("10:00")),
        (parse_time("10:30"), parse_time("11:00")),
        (parse_time("11:30"), parse_time("13:00")),
        (parse_time("14:00"), parse_time("16:00")),
        (parse_time("16:30"), parse_time("17:00"))
    ]
}

# Find all possible free time slots for each participant
def get_free_slots(busy, start, end):
    free_slots = []
    current = start
    for busy_start, busy_end in sorted(busy, key=lambda x: x[0]):
        if current < busy_start:
            free_slots.append((current, busy_start))
        current = max(current, busy_end)
    if current < end:
        free_slots.append((current, end))
    return free_slots

all_free_slots = []
for person in busy_intervals:
    all_free_slots.append(get_free_slots(busy_intervals[person], start_time, end_time))

# Find overlapping free slots across all participants
def find_common_slots(slots_list):
    common = slots_list[0]
    for slots in slots_list[1:]:
        new_common = []
        for c_start, c_end in common:
            for s_start, s_end in slots:
                overlap_start = max(c_start, s_start)
                overlap_end = min(c_end, s_end)
                if overlap_start < overlap_end:
                    new_common.append((overlap_start, overlap_end))
        common = new_common
        if not common:
            break
    return common

common_slots = find_common_slots(all_free_slots)

# Find the first slot that can fit the meeting duration
for slot_start, slot_end in common_slots:
    if (slot_end - slot_start).seconds // 60 >= meeting_duration:
        meeting_start = slot_start
        meeting_end = meeting_start + timedelta(minutes=meeting_duration)
        break

# Format the result
meeting_start_str = meeting_start.strftime("%H:%M")
meeting_end_str = meeting_end.strftime("%H:%M")
print(f"{meeting_start_str}:{meeting_end_str} {day_of_week}")