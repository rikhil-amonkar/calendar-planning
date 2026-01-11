def find_meeting_time(evelyn_availability, randy_unavailable, meeting_duration, work_start, work_end, evelyn_preference_end):
    # Convert all times to minutes since start of the day for easier comparison
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes

    def minutes_to_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    work_start_minutes = time_to_minutes(work_start)
    work_end_minutes = time_to_minutes(work_end)
    evelyn_preference_end_minutes = time_to_minutes(evelyn_preference_end)

    # Randy's available slots
    randy_available_slots = []
    current_start = work_start_minutes

    for start, end in sorted(randy_unavailable):
        start_minutes = time_to_minutes(start)
        end_minutes = time_to_minutes(end)
        if start_minutes > current_start:
            randy_available_slots.append((current_start, start_minutes))
        current_start = max(current_start, end_minutes)

    if current_start < work_end_minutes:
        randy_available_slots.append((current_start, work_end_minutes))

    # Find a suitable slot for both
    for start, end in randy_available_slots:
        if start <= evelyn_preference_end_minutes and end - start >= meeting_duration:
            meeting_start = start
            meeting_end = meeting_start + meeting_duration
            return f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}", "Monday"

    return None, None

# Define the inputs
evelyn_availability = (time_to_minutes("09:00"), time_to_minutes("13:00"))  # Evelyn is available from 9:00 to 13:00
randy_unavailable = [("09:00", "10:30"), ("11:00", "15:30"), ("16:00", "17:00")]
meeting_duration = 30  # Half an hour in minutes
work_start = "09:00"
work_end = "17:00"
evelyn_preference_end = "13:00"

# Find the meeting time
meeting_time, day_of_week = find_meeting_time(evelyn_availability, randy_unavailable, meeting_duration, work_start, work_end, evelyn_preference_end)

if meeting_time:
    print(f"Meeting Time: {meeting_time} on {day_of_week}")
else:
    print("No suitable time found.")