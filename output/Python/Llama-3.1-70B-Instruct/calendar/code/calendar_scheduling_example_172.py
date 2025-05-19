from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, day, start_time, end_time):
    # Convert time to minutes
    start_time_minutes = start_time.hour * 60 + start_time.minute
    end_time_minutes = end_time.hour * 60 + end_time.minute

    # Initialize a list to store the available time slots
    available_time_slots = [True] * ((end_time_minutes - start_time_minutes) // meeting_duration)

    # Iterate over each participant's schedule
    for participant in participants.values():
        for schedule in participant:
            # Convert schedule time to minutes
            schedule_start_minutes = schedule[0].hour * 60 + schedule[0].minute
            schedule_end_minutes = schedule[1].hour * 60 + schedule[1].minute

            # Mark the time slot as unavailable if it overlaps with the participant's schedule
            for i in range((schedule_start_minutes - start_time_minutes) // meeting_duration, (schedule_end_minutes - start_time_minutes) // meeting_duration):
                if 0 <= i < len(available_time_slots):
                    available_time_slots[i] = False

    # Find the first available time slot
    for i, time_slot in enumerate(available_time_slots):
        if time_slot:
            # Calculate the start and end time of the meeting
            meeting_start_time = start_time + timedelta(minutes=i * meeting_duration)
            meeting_end_time = meeting_start_time + timedelta(minutes=meeting_duration)

            return meeting_start_time.strftime("%H:%M") + ":" + meeting_end_time.strftime("%H:%M"), day


# Define the participants' schedules
participants = {
    "Patrick": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Kayla": [(datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
              (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
              (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Carl": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
             (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
             (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
             (datetime.strptime("14:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Christian": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                  (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                  (datetime.strptime("14:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Define the meeting duration, day, start time, and end time
meeting_duration = 30
day = "Monday"
start_time = datetime.strptime("09:00", "%H:%M")
end_time = datetime.strptime("17:00", "%H:%M")

# Find a suitable time for the meeting
meeting_time, meeting_day = find_meeting_time(participants, meeting_duration, day, start_time, end_time)

print(f"Proposed meeting time: {meeting_time} on {meeting_day}")