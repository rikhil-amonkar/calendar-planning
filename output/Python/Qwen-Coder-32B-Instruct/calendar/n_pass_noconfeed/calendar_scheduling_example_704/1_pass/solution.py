def find_meeting_time(larry_schedule, samuel_schedule, preferred_days, meeting_duration):
    # Convert times to minutes from start of the day for easier comparison
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes

    def minutes_to_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    # Define work hours in minutes
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")

    # Process schedules
    larry_busy = []
    samuel_busy = []

    for day in preferred_days:
        if day in larry_schedule:
            larry_busy.extend([(time_to_minutes(start), time_to_minutes(end)) for start, end in larry_schedule[day]])
        if day in samuel_schedule:
            samuel_busy.extend([(time_to_minutes(start), time_to_minutes(end)) for start, end in samuel_schedule[day]])

    # Sort busy times
    larry_busy.sort()
    samuel_busy.sort()

    # Find free slots
    for day in preferred_days:
        current_time = work_start
        if day == 'Monday':
            samuel_busy_day = samuel_busy[:5]
        elif day == 'Tuesday':
            samuel_busy_day = samuel_busy[5:8]
        elif day == 'Wednesday':
            samuel_busy_day = samuel_busy[8:]

        for start, end in samuel_busy_day:
            if current_time + meeting_duration <= start:
                return f"{minutes_to_time(current_time)}:{minutes_to_time(current_time + meeting_duration)}", day
            current_time = max(current_time, end)

        if current_time + meeting_duration <= work_end:
            return f"{minutes_to_time(current_time)}:{minutes_to_time(current_time + meeting_duration)}", day

    return None, None

# Define schedules
larry_schedule = {}
samuel_schedule = {
    'Monday': [('10:30', '11:00'), ('12:00', '12:30'), ('13:00', '15:00'), ('15:30', '16:30')],
    'Tuesday': [('09:00', '12:00'), ('14:00', '15:30'), ('16:30', '17:00')],
    'Wednesday': [('10:30', '11:00'), ('11:30', '12:00'), ('12:30', '13:00'), ('14:00', '14:30'), ('15:00', '16:00')]
}

# Meeting duration in minutes
meeting_duration = 30

# Preferred days in order of preference
preferred_days = ['Monday', 'Tuesday', 'Wednesday']

# Find and print the meeting time
meeting_time, meeting_day = find_meeting_time(larry_schedule, samuel_schedule, preferred_days, meeting_duration)
print(f"{meeting_time} {meeting_day}")