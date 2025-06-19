from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration):
    # Sort participants by earliest end time
    participants.sort(key=lambda x: x[1])

    for start_time in range(9, 17):
        for end_time in range(start_time + 1, 17):
            meeting_start = datetime.strptime(f"{start_time}:00", "%H:%M")
            meeting_end = datetime.strptime(f"{end_time}:00", "%H:%M") + timedelta(minutes=meeting_duration)

            # Check if meeting fits within work hours
            if meeting_start < datetime.strptime("17:00", "%H:%M") and meeting_end > datetime.strptime("9:00", "%H:%M"):
                # Check if meeting conflicts with any participant's schedule
                if all(
                    not (
                        start_time <= x[0].hour < end_time
                        or start_time < x[1].hour < end_time
                        or x[0].hour <= start_time < x[1].hour
                        or x[0].hour < end_time <= x[1].hour
                    )
                    for participant, (start, end) in participants.items()
                ):
                    return f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')} - {datetime.strftime(meeting_end, '%A')}"

    return "No meeting time found"

# Define participants' schedules
participants = {
    "Ronald": ((9, 17),),
    "Stephen": ((10, 10.5), (12, 12.5)),
    "Brittany": ((11, 11.5), (13.5, 14), (15.5, 16), (16.5, 17)),
    "Dorothy": ((9, 9.5), (10, 10.5), (11, 12.5), (13, 15), (15.5, 17)),
    "Rebecca": ((9.5, 10.5), (11, 11.5), (12, 12.5), (13, 17)),
    "Jordan": ((9, 9.5), (10, 11), (11.5, 12), (13, 15), (15.5, 16.5)),
}

# Define meeting duration in minutes
meeting_duration = 30

# Find meeting time
meeting_time = find_meeting_time(participants.items(), meeting_duration)

# Print meeting time
print(meeting_time)