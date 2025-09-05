def get_free_slots(busy_intervals, work_start, work_end):
    # Sort intervals by their start time
    busy_intervals = sorted(busy_intervals, key=lambda x: x[0])
    free_slots = []
    current_start = work_start
    for interval in busy_intervals:
        if interval[0] > current_start:
            free_slots.append((current_start, interval[0]))
        current_start = max(current_start, interval[1])
    if current_start < work_end:
        free_slots.append((current_start, work_end))
    return free_slots

def find_earliest_slot(free1, free2, duration):
    # Look for an intersection between free1 and free2 that is at least 'duration' minutes long.
    for slot1 in free1:
        for slot2 in free2:
            start = max(slot1[0], slot2[0])
            end = min(slot1[1], slot2[1])
            if end - start >= duration:
                return (start, start + duration)
    return None

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Working hours 9:00 to 17:00 in minutes
work_start = 9 * 60     # 540 minutes
work_end = 17 * 60      # 1020 minutes
meeting_duration = 30   # duration in minutes

# Days to consider in order
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

# Define busy schedules in minutes (start, end) for each participant
# Mary has no meetings on Monday.
mary_schedule = {
    "Monday": [],
    "Tuesday": [(10 * 60, 10 * 60 + 30), (15 * 60 + 30, 16 * 60)],
    "Wednesday": [(9 * 60 + 30, 10 * 60), (15 * 60, 15 * 60 + 30)],
    "Thursday": [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60 + 30)]
}

alexis_schedule = {
    "Monday": [(9 * 60, 10 * 60), (10 * 60 + 30, 12 * 60), (12 * 60 + 30, 16 * 60 + 30)],
    "Tuesday": [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60 + 30), (12 * 60, 15 * 60 + 30), (16 * 60, 17 * 60)],
    "Wednesday": [(9 * 60, 11 * 60), (11 * 60 + 30, 17 * 60)],
    "Thursday": [(10 * 60, 12 * 60), (14 * 60, 14 * 60 + 30), (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)]
}

meeting_found = False

for day in days:
    mary_free = get_free_slots(mary_schedule.get(day, []), work_start, work_end)
    alexis_free = get_free_slots(alexis_schedule.get(day, []), work_start, work_end)
    meeting_slot = find_earliest_slot(mary_free, alexis_free, meeting_duration)
    if meeting_slot:
        start_time_str = minutes_to_time(meeting_slot[0])
        end_time_str = minutes_to_time(meeting_slot[1])
        print(f"{day} {{{start_time_str}:{end_time_str}}}")
        meeting_found = True
        break

if not meeting_found:
    print("No available time slot found.")