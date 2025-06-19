def main():
    # Define work hours: 9:00 to 17:00 (480 minutes from 0 to 479)
    total_minutes = 480
    available = [True] * total_minutes  # True means minute is available for meeting

    # Helper function to convert time string to minutes from 9:00
    def time_to_minutes(time_str):
        h, m = time_str.split(':')
        return (int(h) - 9) * 60 + int(m)

    # Busy intervals for each participant
    participants_schedule = {
        "Patrick": ["13:30 to 14:00", "14:30 to 15:00"],
        "Shirley": ["9:00 to 9:30", "11:00 to 11:30", "12:00 to 12:30", "14:30 to 15:00", "16:00 to 17:00"],
        "Jeffrey": ["9:00 to 9:30", "10:30 to 11:00", "11:30 to 12:00", "13:00 to 13:30", "16:00 to 17:00"],
        "Gloria": ["11:30 to 12:00", "15:00 to 15:30"],
        "Nathan": ["9:00 to 9:30", "10:30 to 12:00", "14:00 to 17:00"],
        "Angela": ["9:00 to 9:30", "10:00 to 11:00", "12:30 to 15:00", "15:30 to 16:30"],
        "David": ["9:00 to 9:30", "10:00 to 10:30", "11:00 to 14:00", "14:30 to 16:30"]
    }

    # Mark busy minutes in the available array
    for person, intervals in participants_schedule.items():
        for interval in intervals:
            start_str, end_str = interval.split(' to ')
            start_min = time_to_minutes(start_str)
            end_min = time_to_minutes(end_str)
            # Clamp end_min to 480 (17:00)
            end_min = min(end_min, total_minutes)
            # Mark minutes from start_min to end_min-1 as unavailable
            for minute in range(start_min, end_min):
                if minute < total_minutes:
                    available[minute] = False

    # Find first available 30-minute slot
    meeting_duration = 30
    consecutive_count = 0
    start_slot = -1

    for minute in range(total_minutes):
        if available[minute]:
            consecutive_count += 1
            if consecutive_count >= meeting_duration:
                start_slot = minute - meeting_duration + 1
                break
        else:
            consecutive_count = 0

    # Convert start_slot back to time string
    def minutes_to_time(minutes):
        total = minutes
        hour = 9 + total // 60
        minute = total % 60
        return f"{hour:02d}:{minute:02d}"

    start_time = minutes_to_time(start_slot)
    end_time = minutes_to_time(start_slot + meeting_duration)

    # Output day and time range in HH:MM:HH:MM format
    print("Monday")
    print(f"{start_time}:{end_time}")

if __name__ == "__main__":
    main()