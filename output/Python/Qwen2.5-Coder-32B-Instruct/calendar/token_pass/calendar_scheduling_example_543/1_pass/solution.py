from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def find_free_slots(busy_times, start, end):
    free_slots = []
    current_start = start
    for busy_start, busy_end in busy_times:
        if current_start < busy_start:
            free_slots.append((current_start, busy_start))
        current_start = busy_end
    if current_start < end:
        free_slots.append((current_start, end))
    return free_slots

def find_common_slots(slots_list):
    if not slots_list:
        return []

    # Start with the first person's slots
    common_slots = slots_list[0]

    for slots in slots_list[1:]:
        new_common_slots = []
        for start1, end1 in common_slots:
            for start2, end2 in slots:
                overlap_start = max(start1, start2)
                overlap_end = min(end1, end2)
                if overlap_start < overlap_end:
                    new_common_slots.append((overlap_start, overlap_end))
        common_slots = new_common_slots

    return common_slots

def find_meeting_slot(participants_busy_times, day, meeting_duration):
    start_of_day = parse_time("09:00")
    end_of_day = parse_time("17:00")
    meeting_duration_timedelta = timedelta(hours=meeting_duration)

    # Parse and sort busy times for each participant
    parsed_busy_times = []
    for busy_times in participants_busy_times:
        parsed_busy_times.append(sorted([(parse_time(start), parse_time(end)) for start, end in busy_times]))

    # Find free slots for each participant
    free_slots = [find_free_slots(busy_times, start_of_day, end_of_day) for busy_times in parsed_busy_times]

    # Find common free slots
    common_free_slots = find_common_slots(free_slots)

    # Find a slot that fits the meeting duration
    for start, end in common_free_slots:
        if end - start >= meeting_duration_timedelta:
            return start.strftime("%H:%M"), end.strftime("%H:%M"), day

    return None

# Define busy times for James and John
james_busy_times = [("11:30", "12:00"), ("14:30", "15:00")]
john_busy_times = [("09:30", "11:00"), ("11:30", "12:00"), ("12:30", "13:30"), ("14:30", "16:30")]

# Find a suitable meeting time
meeting_time = find_meeting_slot([james_busy_times, john_busy_times], "Monday", 1)

if meeting_time:
    print(f"Meeting time: {meeting_time[0]}:{meeting_time[1]} on {meeting_time[2]}")
else:
    print("No suitable meeting time found.")