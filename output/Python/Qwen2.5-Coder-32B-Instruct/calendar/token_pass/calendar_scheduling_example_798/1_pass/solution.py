# Define the schedules for Nancy and Jose
nancy_schedule = {
    'Monday': [(9, 10), (10.5, 11.5), (12.5, 13.5)],
    'Tuesday': [(9, 9.5), (11, 11.5), (12, 12.5), (13, 13.5), (16, 17)],
    'Wednesday': [(9, 10), (11.5, 13.5)]
}

jose_schedule = {
    'Monday': [],
    'Tuesday': [],
    'Wednesday': [(9.5, 10), (12.5, 13.5), (14.5, 15)]
}

# Function to find overlapping intervals between two lists of intervals
def find_overlaps(intervals1, intervals2):
    overlaps = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        start_max = max(intervals1[i][0], intervals2[j][0])
        end_min = min(intervals1[i][1], intervals2[j][1])
        if start_max < end_min:
            overlaps.append((start_max, end_min))
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return overlaps

# Find the common free time slots for both Nancy and Jose
common_free_slots = {}
for day in ['Monday', 'Tuesday', 'Wednesday']:
    common_free_slots[day] = find_overlaps(nancy_schedule[day], jose_schedule[day])

# Find the earliest slot that fits the required meeting duration of 0.5 hours
meeting_duration = 0.5
earliest_slot = None
for day in ['Monday', 'Tuesday', 'Wednesday']:
    for slot in common_free_slots[day]:
        if slot[1] - slot[0] >= meeting_duration:
            earliest_slot = (slot, day)
            break
    if earliest_slot:
        break

# Convert the time back to HH:MM format
if earliest_slot:
    slot, day = earliest_slot
    start_hour, start_minute = int(slot[0]), int((slot[0] - int(slot[0])) * 60)
    end_hour, end_minute = int(slot[1]), int((slot[1] - int(slot[1])) * 60)
    print(f"{day} {start_hour:02}:{start_minute:02}:{end_hour:02}:{end_minute:02}")
else:
    print("No suitable time found")