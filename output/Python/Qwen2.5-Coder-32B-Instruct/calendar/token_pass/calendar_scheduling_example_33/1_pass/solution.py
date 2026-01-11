def find_meeting_time(participants, meeting_duration, day_of_week):
    # Helper function to convert time from "HH:MM" format to integer
    def time_to_int(time_str):
        return int(time_str.replace(":", ""))

    # Helper function to convert time from integer back to "HH:MM" format
    def int_to_time(time_int):
        return f"{time_int // 100:02}:{time_int % 100:02}"

    # Define work hours in integer format
    start_work = time_to_int("09:00")
    end_work = time_to_int("17:00")

    # Calculate available slots for each participant
    available_slots = {}
    for name, schedule in participants.items():
        slots = []
        current_start = start_work
        for meeting in sorted(schedule):
            meeting_start, meeting_end = map(time_to_int, meeting.split("-"))
            if current_start < meeting_start:
                slots.append((current_start, meeting_start))
            current_start = max(current_start, meeting_end)
        if current_start < end_work:
            slots.append((current_start, end_work))
        available_slots[name] = slots

    # Find common available slots
    common_slots = available_slots[list(available_slots.keys())[0]]
    for slots in list(available_slots.values())[1:]:
        common_slots = [(max(s1[0], s2[0]), min(s1[1], s2[1])) for s1 in common_slots for s2 in slots if max(s1[0], s2[0]) < min(s1[1], s2[1])]

    # Filter slots based on constraints
    filtered_slots = []
    for slot in common_slots:
        slot_start, slot_end = slot
        if slot_end - slot_start >= meeting_duration:
            # Check Bobby's constraint
            if 'Bobby' in participants and slot_start >= time_to_int("15:00"):
                continue
            filtered_slots.append(slot)

    # Select the first valid slot
    if filtered_slots:
        best_slot = filtered_slots[0]
        best_slot_start = int_to_time(best_slot[0])
        best_slot_end = int_to_time(best_slot[1] - meeting_duration + 60)
        return f"{best_slot_start}:{best_slot_end} {day_of_week}"
    else:
        return "No suitable time found"

# Participants' schedules
participants = {
    "Lisa": ["09:00-10:00", "10:30-11:30", "12:30-13:00", "16:00-16:30"],
    "Bobby": ["09:00-09:30", "10:00-10:30", "11:30-12:00", "15:00-15:30"],
    "Randy": ["09:30-10:00", "10:30-11:00", "11:30-12:30", "13:00-13:30", "14:30-15:30", "16:00-16:30"]
}

meeting_duration = 30  # Meeting duration in minutes
day_of_week = "Monday"

# Find and print the meeting time
print(find_meeting_time(participants, meeting_duration, day_of_week))