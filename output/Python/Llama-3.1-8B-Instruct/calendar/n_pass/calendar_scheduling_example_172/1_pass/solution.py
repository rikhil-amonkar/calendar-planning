from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration):
    # Define the start and end of the work hours
    start_time = datetime.strptime('09:00', '%H:%M')
    end_time = datetime.strptime('17:00', '%H:%M')

    # Find the earliest available time slot for all participants
    for hour in range(start_time.hour, end_time.hour):
        for minute in range(0, 60, meeting_duration):
            time = datetime.combine(datetime.today(), datetime.min.time() + timedelta(hours=hour, minutes=minute))
            time_end = time + timedelta(minutes=meeting_duration)

            # Check if the time slot is available for all participants
            if all(not (time < datetime.strptime(participant['busy'][i], '%H:%M') and 
                       datetime.strptime(participant['busy'][i], '%H:%M') < time_end) 
                   for i, participant in enumerate(participants) for j in range(len(participant['busy']))):
                return f"{time.strftime('%H:%M')}-{time_end.strftime('%H:%M')} on {datetime.today().strftime('%A')}"

    return "No available time slot found"

# Define the participants' schedules
participants = {
    'Patrick': {'busy': ['09:00-09:30', '10:00-10:30', '13:30-14:00', '16:00-16:30']},
    'Kayla': {'busy': ['12:30-13:30', '15:00-15:30', '16:00-16:30']},
    'Carl': {'busy': ['10:30-11:00', '12:00-12:30', '13:00-13:30', '14:30-17:00']},
    'Christian': {'busy': ['09:00-12:30', '13:00-14:00', '14:30-17:00']}
}

# Find the meeting time
meeting_duration = 30  # in minutes
print(find_meeting_time(participants.values(), meeting_duration))