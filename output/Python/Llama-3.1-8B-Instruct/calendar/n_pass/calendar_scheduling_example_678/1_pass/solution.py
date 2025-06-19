from datetime import datetime, timedelta

def find_meeting_time(russell_schedule, alexander_schedule, meeting_duration, day, russell_preference):
    # Find available time slots for Russell
    russell_available = []
    for start, end in russell_schedule:
        russell_available.append((start, end))

    # Find available time slots for Alexander
    alexander_available = []
    for start, end in alexander_schedule:
        alexander_available.append((start, end))

    # Filter available time slots based on the day and Russell's preference
    russell_available_day = [slot for slot in russell_available if slot[0].date() == day.date()]
    alexander_available_day = [slot for slot in alexander_available if slot[0].date() == day.date()]

    # Combine available time slots for both participants
    combined_available = []
    for russell_slot in russell_available_day:
        for alexander_slot in alexander_available_day:
            combined_available.append((max(russell_slot[0], alexander_slot[0]), min(russell_slot[1], alexander_slot[1])))

    # Find overlapping time slots that are long enough for the meeting
    meeting_time_slots = []
    for slot in combined_available:
        if slot[1] - slot[0] >= meeting_duration:
            meeting_time_slots.append(slot)

    # Sort time slots by start time
    meeting_time_slots.sort(key=lambda x: x[0])

    # Find the first time slot that meets the meeting duration and Russell's preference
    for slot in meeting_time_slots:
        if slot[1] - slot[0] == meeting_duration and (slot[0] >= datetime(day.year, day.month, day.day, 13, 30).replace(minute=0, second=0) or russell_preference == False):
            return f"{slot[0].strftime('%H:%M')}:{slot[1].strftime('%H:%M')} on {day.strftime('%A')}"

    return "No available time slots found"

# Define schedules and constraints
russell_schedule = [(datetime(2024, 7, 22, 10, 30), datetime(2024, 7, 22, 11, 0)), (datetime(2024, 7, 23, 13, 0), datetime(2024, 7, 23, 13, 30))]
alexander_schedule = [(datetime(2024, 7, 22, 9, 0), datetime(2024, 7, 22, 11, 30)), (datetime(2024, 7, 22, 12, 0), datetime(2024, 7, 22, 14, 30)), (datetime(2024, 7, 22, 15, 0), datetime(2024, 7, 22, 17, 0)), (datetime(2024, 7, 23, 9, 0), datetime(2024, 7, 23, 10, 0)), (datetime(2024, 7, 23, 13, 0), datetime(2024, 7, 23, 14, 0)), (datetime(2024, 7, 23, 15, 0), datetime(2024, 7, 23, 15, 30)), (datetime(2024, 7, 23, 16, 0), datetime(2024, 7, 23, 16, 30))]
meeting_duration = timedelta(hours=1)
day = datetime(2024, 7, 23)
russell_preference = True

print(find_meeting_time(russell_schedule, alexander_schedule, meeting_duration, day, russell_preference))