day_start = 9 * 60
day_end = 17 * 60
meeting_duration = 30

# Define busy intervals for each participant
megan = [(9*60, 9*60 + 30), (10*60, 11*60), (12*60, 12*60 + 30)]
christine = [(9*60, 9*60 + 30), (11*60 + 30, 12*60), (13*60, 14*60), (15*60 + 30, 16*60 + 30)]
gabriel = []
sara = [(11*60 + 30, 12*60), (14*60 + 30, 15*60)]
bruce = [(9*60 + 30, 10*60), (10*60 + 30, 12*60), (12*60 + 30, 14*60), (14*60 + 30, 15*60), (15*60 + 30, 16*60 + 30)]
kathryn = [(10*60, 15*60 + 30), (16*60, 16*60 + 30)]
billy = [(9*60, 9*60 + 30), (11*60, 11*60 + 30), (12*60, 14*60), (14*60 + 30, 15*60 + 30)]

all_intervals = megan + christine + gabriel + sara + bruce + kathryn + billy

# Sort intervals by start time
sorted_intervals = sorted(all_intervals, key=lambda x: x[0])

# Merge intervals
merged = []
for interval in sorted_intervals:
    if not merged:
        merged.append(interval)
    else:
        last_start, last_end = merged[-1]
        current_start, current_end = interval
        if current_start <= last_end:
            # Overlapping or adjacent, merge
            new_start = last_start
            new_end = max(last_end, current_end)
            merged[-1] = (new_start, new_end)
        else:
            merged.append(interval)

# Find free slots
free_slots = []
prev_end = day_start

for interval in merged:
    start, end = interval
    if start > prev_end:
        free_start = prev_end
        free_end = start
        if free_end - free_start >= meeting_duration:
            free_slots.append((free_start, free_end))
    prev_end = max(prev_end, end)

# Check after last interval
if day_end > prev_end:
    if day_end - prev_end >= meeting_duration:
        free_slots.append((prev_end, day_end))

# Get the first free slot
if free_slots:
    first_slot = free_slots[0]
    start_time = first_slot[0]
    end_time = start_time + meeting_duration

    # Convert to time strings
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    time_str = f"{format_time(start_time)}:{format_time(end_time)}"
    day_str = "Monday"
    print(f"{time_str} {day_str}")
else:
    print("No available time slot found")