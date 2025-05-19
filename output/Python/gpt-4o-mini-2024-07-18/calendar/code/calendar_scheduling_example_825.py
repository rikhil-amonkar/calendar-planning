from datetime import datetime, timedelta

def find_meeting_time():
    # Define work hours and days
    work_hours = {
        'Monday': [(9, 17)],
        'Tuesday': [(9, 17)],
        'Wednesday': [(9, 17)],
        'Thursday': [(9, 17)]
    }

    # Existing schedules for Laura
    laura_busy = {
        'Monday': [(10, 30, 11, 0), (12, 30, 13, 0), (14, 30, 15, 30), (16, 0, 17, 0)],
        'Tuesday': [(9, 30, 10, 0), (11, 0, 11, 30), (13, 0, 13, 30), (14, 30, 15, 0), (16, 0, 17, 0)],
        'Wednesday': [(11, 30, 12, 0), (12, 30, 13, 0), (15, 30, 16, 30)],
        'Thursday': [(10, 30, 11, 0), (12, 0, 13, 30), (15, 0, 15, 30), (16, 0, 16, 30)]
    }

    # Existing schedules for Philip
    philip_busy = {
        'Monday': [(9, 0, 17, 0)],
        'Tuesday': [(9, 0, 11, 0), (11, 30, 12, 0), (13, 0, 13, 30), (14, 0, 14, 30), (15, 0, 16, 30)],
        'Wednesday': [(9, 0, 10, 0), (11, 0, 12, 0), (12, 30, 16, 0), (16, 30, 17, 0)],
        'Thursday': [(9, 0, 10, 30), (11, 0, 12, 30), (13, 0, 17, 0)]
    }

    # Define meeting duration
    meeting_duration = 1  # in hours

    # Function to check if a time slot is available
    def is_time_slot_available(day, start_hour, end_hour):
        for start, end in laura_busy.get(day, []):
            if not (end_hour <= start or end <= start_hour):
                return False
        for start, end in philip_busy.get(day, []):
            if not (end_hour <= start or end <= start_hour):
                return False
        return True

    # Find suitable time
    for day, hours in work_hours.items():
        for start_hour, end_hour in hours:
            for hour in range(start_hour, end_hour - meeting_duration + 1):
                if is_time_slot_available(day, hour, hour + meeting_duration):
                    start_time = f"{hour:02}:00"
                    end_time = f"{hour + meeting_duration:02}:00"
                    return f"{start_time}:{end_time} on {day}"

# Execute the function to get the meeting time
print(find_meeting_time())