from datetime import datetime, timedelta

def find_meeting_time(russell_schedule, alexander_schedule, meeting_duration, day, russell_preference):
    """
    Find the first available time slot that meets the meeting duration.

    Args:
        russell_schedule (list): Russell's schedule as a list of tuples.
        alexander_schedule (list): Alexander's schedule as a list of tuples.
        meeting_duration (timedelta): The duration of the meeting.
        day (datetime): The day to find the meeting time for.
        russell_preference (bool): Whether Russell prefers afternoon meetings.

    Returns:
        str: The first available time slot that meets the meeting duration, or "No available time slots found" if none are available.
    """

    # Find available time slots for Russell
    russell_available = [(start, end) for start, end in russell_schedule if start.date() == day.date() and end.date() == day.date()]

    # Find available time slots for Alexander
    alexander_available = [(start, end) for start, end in alexander_schedule if start.date() == day.date() and end.date() == day.date()]

    # Filter available time slots based on Russell's preference
    russell_available_day = [slot for slot in russell_available if slot[0].date() == day.date() and (russell_preference and slot[0].hour >= 13 and slot[0].minute >= 30 or not russell_preference)]

    # Filter available time slots based on Alexander's schedule
    alexander_available_day = [slot for slot in alexander_available if slot[0].date() == day.date()]

    # Combine available time slots for both participants
    combined_available = []
    for russell_slot in russell_available_day:
        for alexander_slot in alexander_available_day:
            # Check for overlapping time slots
            overlap_start = max(russell_slot[0], alexander_slot[0])
            overlap_end = min(russell_slot[1], alexander_slot[1])
            if overlap_start < overlap_end:
                combined_available.append((overlap_start, overlap_end))

    # Find overlapping time slots that are long enough for the meeting
    meeting_time_slots = []
    for slot in combined_available:
        if slot[1] - slot[0] >= meeting_duration:
            meeting_time_slots.append(slot)

    # Find the first time slot that meets the meeting duration
    if meeting_time_slots:
        return f"{meeting_time_slots[0][0].strftime('%H:%M')} - {meeting_time_slots[0][1].strftime('%H:%M')} on {day.strftime('%A')}"
    else:
        return "No available time slots found"

# Define schedules and constraints
russell_schedule = [(datetime(2024, 7, 22, 10, 30), datetime(2024, 7, 22, 11, 0)), (datetime(2024, 7, 23, 13, 0), datetime(2024, 7, 23, 13, 30))]
alexander_schedule = [(datetime(2024, 7, 22, 9, 0), datetime(2024, 7, 22, 11, 30)), (datetime(2024, 7, 22, 12, 0), datetime(2024, 7, 22, 14, 30)), (datetime(2024, 7, 22, 15, 0), datetime(2024, 7, 22, 17, 0)), (datetime(2024, 7, 23, 9, 0), datetime(2024, 7, 23, 10, 0)), (datetime(2024, 7, 23, 13, 0), datetime(2024, 7, 23, 14, 0)), (datetime(2024, 7, 23, 15, 0), datetime(2024, 7, 23, 15, 30)), (datetime(2024, 7, 23, 16, 0), datetime(2024, 7, 23, 16, 30))]
meeting_duration = timedelta(hours=1)
day = datetime(2024, 7, 23)
russell_preference = True

print(find_meeting_time(russell_schedule, alexander_schedule, meeting_duration, day, russell_preference))