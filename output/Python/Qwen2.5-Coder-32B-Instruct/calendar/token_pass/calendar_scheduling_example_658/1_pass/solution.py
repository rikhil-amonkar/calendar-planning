def find_meeting_time(shirley_schedule, albert_schedule, meeting_duration, preferred_day=None, preferred_end_time=None):
    def parse_time(time_str):
        return int(time_str[:2]), int(time_str[3:])

    def generate_free_slots(schedule, start_time="09:00", end_time="17:00"):
        start_hour, start_minute = parse_time(start_time)
        end_hour, end_minute = parse_time(end_time)
        current_hour, current_minute = start_hour, start_minute
        free_slots = []
        for event_start, event_end in sorted(schedule.items()):
            event_start_hour, event_start_minute = parse_time(event_start)
            event_end_hour, event_end_minute = parse_time(event_end)
            if current_hour < event_start_hour or (current_hour == event_start_hour and current_minute < event_start_minute):
                free_slots.append((f"{current_hour:02}:{current_minute:02}", f"{event_start_hour:02}:{event_start_minute:02}"))
            current_hour, current_minute = event_end_hour, event_end_minute
        if current_hour < end_hour or (current_hour == end_hour and current_minute < end_minute):
            free_slots.append((f"{current_hour:02}:{current_minute:02}", end_time))
        return free_slots

    def find_common_slots(shirley_free, albert_free):
        common_slots = []
        i, j = 0, 0
        while i < len(shirley_free) and j < len(albert_free):
            shirley_start, shirley_end = shirley_free[i]
            albert_start, albert_end = albert_free[j]
            max_start = max(shirley_start, albert_start)
            min_end = min(shirley_end, albert_end)
            if parse_time(max_start) < parse_time(min_end):
                common_slots.append((max_start, min_end))
            if parse_time(shirley_end) <= parse_time(albert_end):
                i += 1
            else:
                j += 1
        return common_slots

    def filter_slots(slots, duration, preferred_day=None, preferred_end_time=None):
        filtered_slots = []
        for day, day_slots in slots.items():
            if preferred_day and day != preferred_day:
                continue
            for start, end in day_slots:
                start_hour, start_minute = parse_time(start)
                end_hour, end_minute = parse_time(end)
                slot_duration = (end_hour - start_hour) * 60 + (end_minute - start_minute)
                if slot_duration >= duration:
                    if preferred_end_time and parse_time(end) > parse_time(preferred_end_time):
                        continue
                    filtered_slots.append((day, start, end))
        return filtered_slots

    shirley_slots = {
        "Monday": generate_free_slots(shirley_schedule["Monday"]),
        "Tuesday": generate_free_slots(shirley_schedule["Tuesday"])
    }
    albert_slots = {
        "Monday": generate_free_slots(albert_schedule["Monday"]),
        "Tuesday": generate_free_slots(albert_schedule["Tuesday"])
    }

    common_slots = {
        "Monday": find_common_slots(shirley_slots["Monday"], albert_slots["Monday"]),
        "Tuesday": find_common_slots(shirley_slots["Tuesday"], albert_slots["Tuesday"])
    }

    filtered_slots = filter_slots(common_slots, meeting_duration, preferred_day, preferred_end_time)

    if not filtered_slots:
        return "No suitable time found"

    # Return the first suitable slot
    day, start, end = filtered_slots[0]
    return f"{start}:{end} {day}"

# Define the schedules
shirley_schedule = {
    "Monday": {"10:30": "11:00", "12:00": "12:30", "16:00": "16:30"},
    "Tuesday": {"09:30": "10:00"}
}

albert_schedule = {
    "Monday": {"09:00": "17:00"},
    "Tuesday": {"09:30": "11:00", "11:30": "12:30", "13:00": "16:00", "16:30": "17:00"}
}

# Meeting details
meeting_duration = 30  # in minutes
preferred_day = "Tuesday"
preferred_end_time = "10:30"

# Find the meeting time
meeting_time = find_meeting_time(shirley_schedule, albert_schedule, meeting_duration, preferred_day, preferred_end_time)
print(meeting_time)