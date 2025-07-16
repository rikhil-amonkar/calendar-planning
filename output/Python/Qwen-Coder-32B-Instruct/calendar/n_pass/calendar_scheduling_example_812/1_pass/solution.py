from datetime import datetime, timedelta

def find_meeting_time(schedules, duration, start_time, end_time, days):
    def parse_time(time_str):
        return datetime.strptime(time_str, "%H:%M")

    def time_range_to_str(start, end):
        return f"{start.strftime('%H:%M')}:{end.strftime('%H:%M')}"

    duration = timedelta(minutes=duration)
    start_time = parse_time(start_time)
    end_time = parse_time(end_time)

    for day in days:
        available_slots = []
        current_start = start_time

        for event in sorted(schedules[day], key=lambda x: x[0]):
            event_start, event_end = parse_time(event[0]), parse_time(event[1])
            if current_start < event_start and event_start - current_start >= duration:
                available_slots.append((current_start, event_start))
            current_start = max(current_start, event_end)

        if current_start < end_time and end_time - current_start >= duration:
            available_slots.append((current_start, end_time))

        for slot_start, slot_end in available_slots:
            if slot_end - slot_start >= duration:
                return time_range_to_str(slot_start, slot_start + duration), day

    return None, None

# Define the schedules
schedules = {
    "Monday": [("9:00", "10:00"), ("10:30", "12:00"), ("12:30", "16:30")],
    "Tuesday": [("10:00", "10:30"), ("12:00", "15:30"), ("15:30", "16:00"), ("16:00", "17:00")],
    "Wednesday": [("9:00", "11:00"), ("11:30", "17:00")],
    "Thursday": [("9:00", "10:00"), ("10:30", "11:30"), ("12:00", "12:30"), ("14:00", "14:30"), ("15:30", "16:00"), ("16:30", "17:00")]
}

# Meeting parameters
meeting_duration = 30
work_start_time = "9:00"
work_end_time = "17:00"
working_days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

# Find a suitable meeting time
meeting_time, meeting_day = find_meeting_time(schedules, meeting_duration, work_start_time, work_end_time, working_days)

# Output the result
if meeting_time and meeting_day:
    print(f"{meeting_time} on {meeting_day}")
else:
    print("No available time found.")