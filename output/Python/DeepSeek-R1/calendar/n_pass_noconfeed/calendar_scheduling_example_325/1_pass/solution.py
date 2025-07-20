def main():
    total_minutes_in_day = 480
    timeline = [False] * total_minutes_in_day
    max_start_minute = 360  # Meeting must start by 15:00 (360 minutes from 9:00) to end by 15:30

    # Busy intervals in minutes (start, end) - end is exclusive
    jose = [(120, 150), (210, 240)]
    keith = [(300, 330), (360, 390)]
    logan = [(0, 60), (180, 210), (360, 390)]
    megan = [(0, 90), (120, 180), (240, 270), (330, 450)]
    gary = [(0, 30), (60, 90), (150, 240), (270, 300), (330, 450)]
    bobby = [(120, 150), (180, 210), (240, 420)]
    
    all_intervals = jose + keith + logan + megan + gary + bobby

    for start, end in all_intervals:
        for minute in range(start, min(end, total_minutes_in_day)):
            timeline[minute] = True

    start_minute = -1
    for i in range(0, max_start_minute + 1):
        if i + 30 > total_minutes_in_day:
            break
        if not any(timeline[i:i+30]):
            start_minute = i
            break

    if start_minute == -1:
        print("Monday")
        print("No suitable slot found")
    else:
        start_hour = 9 + start_minute // 60
        start_min = start_minute % 60
        end_minute_val = start_minute + 30
        end_hour = 9 + end_minute_val // 60
        end_min = end_minute_val % 60
        time_str = f"{start_hour}:{start_min:02d}:{end_hour}:{end_min:02d}"
        print("Monday")
        print(time_str)

if __name__ == "__main__":
    main()