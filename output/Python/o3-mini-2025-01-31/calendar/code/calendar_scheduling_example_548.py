from datetime import datetime, timedelta, time

def main():
    # Meeting duration: 30 minutes.
    meeting_duration = timedelta(minutes=30)
    
    # Work hours: 09:00 to 17:00 (Monday).
    work_day_start = time(9, 0)
    work_day_end = time(17, 0)
    
    # Participant schedules:
    # Judy is free all day.
    # Nicole's meetings on Monday:
    #   09:00 to 10:00 and 10:30 to 16:30.
    # Nicole prefers not to meet before 16:00.
    
    # Nicole's available slot is after her meeting ends at 16:30,
    # which is within the work day. The available free time is from 16:30 to 17:00.
    # This slot is after 16:00, satisfying Nicole's preference.
    
    # Calculate meeting start and end times based on the available slot.
    meeting_start = datetime.combine(datetime.today(), time(16, 30))
    meeting_end = meeting_start + meeting_duration
    
    # Format the meeting time range as HH:MM:HH:MM.
    meeting_time_range = f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}"
    
    # Day of the week for this meeting.
    meeting_day = "Monday"
    
    # Output the meeting time range and day.
    print(meeting_time_range, meeting_day)

if __name__ == "__main__":
    main()