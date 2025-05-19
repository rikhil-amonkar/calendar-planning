from datetime import datetime, timedelta

def find_meeting_time():
    # Define working hours
    start_time = datetime.strptime("09:00", "%H:%M")
    end_time = datetime.strptime("17:00", "%H:%M")

    # Deborah's availability (all day)
    deborah_availability = [(start_time, end_time)]

    # Albert's blocked times
    albert_busy_times = [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
        (datetime.strptime("10:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
        (datetime.strptime("15:00", "%H:%M"), datetime.strptime("16:30", "%H:%M")),
    ]
    
    # Duration of the meeting
    meeting_duration = timedelta(minutes=30)

    # Check for available slots
    for start, end in deborah_availability:
        current_start = start
        while current_start + meeting_duration <= end:
            # Check if current time conflicts with Albert's busy times
            conflict = False
            for busy_start, busy_end in albert_busy_times:
                if current_start < busy_end and (current_start + meeting_duration) > busy_start:
                    conflict = True
                    break
            if not conflict:
                # Proposed time found
                proposed_start = current_start.strftime("%H:%M")
                proposed_end = (current_start + meeting_duration).strftime("%H:%M")
                return f"{proposed_start}:{proposed_end} Monday"
            current_start += timedelta(minutes=1)

print(find_meeting_time())