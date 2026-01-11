def find_meeting_time(participants, meeting_duration, start_time, end_time):
    # Step 1: Define all possible time slots
    import datetime

    def generate_time_slots(start, end, duration):
        current = start
        slots = []
        while current < end:
            next_slot = current + duration
            slots.append((current, next_slot))
            current = next_slot
        return slots

    # Convert start_time and end_time to datetime objects
    start_datetime = datetime.datetime.strptime(start_time, "%H:%M")
    end_datetime = datetime.datetime.strptime(end_time, "%H:%M")
    meeting_duration_timedelta = datetime.timedelta(minutes=meeting_duration)

    all_slots = generate_time_slots(start_datetime, end_datetime, meeting_duration_timedelta)

    # Step 2: Parse the constraints
    def parse_busy_times(busy_times):
        busy_slots = []
        for busy_time in busy_times:
            start, end = busy_time.split(" to ")
            start_dt = datetime.datetime.strptime(start, "%H:%M")
            end_dt = datetime.datetime.strptime(end, "%H:%M")
            busy_slots.extend(generate_time_slots(start_dt, end_dt, meeting_duration_timedelta))
        return busy_slots

    busy_slots_by_person = {name: parse_busy_times(busy_times) for name, busy_times in participants.items()}

    # Step 3: Identify free slots
    all_busy_slots = set(slot for slots in busy_slots_by_person.values() for slot in slots)
    all_slots_set = set(all_slots)
    free_slots = all_slots_set - all_busy_slots

    # Step 4: Select a suitable slot
    if free_slots:
        # Since the problem guarantees a solution exists, we can just take the first one
        chosen_slot = sorted(free_slots)[0]
        start_time_str = chosen_slot[0].strftime("%H:%M")
        end_time_str = chosen_slot[1].strftime("%H:%M")
        return f"{start_time_str}:{end_time_str} Monday"
    else:
        return "No available time slot found"

# Participants' schedules
participants = {
    "Walter": [],
    "Cynthia": ["9:00 to 9:30", "10:00 to 10:30", "13:30 to 14:30", "15:00 to 16:00"],
    "Ann": ["10:00 to 11:00", "13:00 to 13:30", "14:00 to 15:00", "16:00 to 16:30"],
    "Catherine": ["9:00 to 11:30", "12:30 to 13:30", "14:30 to 17:00"],
    "Kyle": ["9:00 to 9:30", "10:00 to 11:30", "12:00 to 12:30", "13:00 to 14:30", "15:00 to 16:00"]
}

# Meeting details
meeting_duration = 30  # in minutes
start_time = "9:00"
end_time = "17:00"

# Find and print the meeting time
print(find_meeting_time(participants, meeting_duration, start_time, end_time))