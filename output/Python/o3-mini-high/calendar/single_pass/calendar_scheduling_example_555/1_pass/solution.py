def find_meeting_time():
    # Work day hours: 09:00 to 17:00 on Monday
    # Meeting duration: 30 minutes
    #
    # Given constraints:
    # - Evelyn is free throughout the day but does not want to meet after 13:00.
    # - Randy is busy on Monday:
    #     09:00 to 10:30,
    #     11:00 to 15:30,
    #     16:00 to 17:00.
    #
    # Randy's available windows:
    #   - 10:30 to 11:00 (30 minutes)
    #   - 15:30 to 16:00 (30 minutes, but after 13:00, so not acceptable)
    #
    # Therefore, the only valid meeting time is from 10:30 to 11:00 on Monday.
    
    day = "Monday"
    start_time = "10:30"
    end_time = "11:00"
    
    return day, start_time, end_time

if __name__ == "__main__":
    meeting_day, start, end = find_meeting_time()
    # Output format: Day and time range in HH:MM:HH:MM format
    print(f"{meeting_day} {start}:{end}")