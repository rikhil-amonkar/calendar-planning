def main():
    # Convert time string to minutes since 9:00
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return (h - 9) * 60 + m

    # Convert minutes since 9:00 back to time string
    def minutes_to_time(minutes):
        h = 9 + minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    # Initialize timeline (480 minutes from 9:00 to 17:00)
    timeline = [0] * 480

    # Define busy intervals for each participant (in minutes since 9:00)
    busy_intervals = {
        'Stephen': [(time_to_minutes('10:00'), time_to_minutes('10:30')),
                    (time_to_minutes('12:00'), time_to_minutes('12:30'))],
        'Brittany': [(time_to_minutes('11:00'), time_to_minutes('11:30')),
                     (time_to_minutes('13:30'), time_to_minutes('14:00')),
                     (time_to_minutes('15:30'), time_to_minutes('16:00')),
                     (time_to_minutes('16:30'), time_to_minutes('17:00'))],
        'Dorothy': [(time_to_minutes('9:00'), time_to_minutes('9:30')),
                    (time_to_minutes('10:00'), time_to_minutes('10:30')),
                    (time_to_minutes('11:00'), time_to_minutes('12:30')),
                    (time_to_minutes('13:00'), time_to_minutes('15:00')),
                    (time_to_minutes('15:30'), time_to_minutes('17:00'))],
        'Rebecca': [(time_to_minutes('9:30'), time_to_minutes('10:30')),
                    (time_to_minutes('11:00'), time_to_minutes('11:30')),
                    (time_to_minutes('12:00'), time_to_minutes('12:30')),
                    (time_to_minutes('13:00'), time_to_minutes('17:00'))],
        'Jordan': [(time_to_minutes('9:00'), time_to_minutes('9:30')),
                   (time_to_minutes('10:00'), time_to_minutes('11:00')),
                   (time_to_minutes('11:30'), time_to_minutes('12:00')),
                   (time_to_minutes('13:00'), time_to_minutes('15:00')),
                   (time_to_minutes('15:30'), time_to_minutes('16:30'))]
    }

    # Mark busy times on the timeline
    for intervals in busy_intervals.values():
        for start, end in intervals:
            for minute in range(start, end):
                if minute < 480:
                    timeline[minute] = 1

    # Find a 30-minute free slot
    meeting_duration = 30
    for start_minute in range(0, 480 - meeting_duration + 1):
        if all(timeline[i] == 0 for i in range(start_minute, start_minute + meeting_duration)):
            start_time = minutes_to_time(start_minute)
            end_time = minutes_to_time(start_minute + meeting_duration)
            print(f"Monday:{start_time}:{end_time}")
            return

    print("No suitable time found")

if __name__ == "__main__":
    main()