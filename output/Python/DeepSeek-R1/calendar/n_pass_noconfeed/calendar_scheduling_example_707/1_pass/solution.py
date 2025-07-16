def min_to_time(m):
    total_minutes = 9 * 60 + m
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Define the busy intervals in minutes from 9:00 for each participant and day
    # Monday
    ryan_monday = [(30, 60), (120, 180), (240, 270), (390, 420)]  # 9:30-10:00, 11:00-12:00, 13:00-13:30, 15:30-16:00
    adam_monday = [(0, 90), (120, 270), (300, 420), (450, 480)]    # 9:00-10:30, 11:00-13:30, 14:00-16:00, 16:30-17:00
    
    # Tuesday
    ryan_tuesday = [(150, 210), (390, 420)]                        # 11:30-12:30, 15:30-16:00
    adam_tuesday = [(0, 60), (90, 390), (420, 480)]                # 9:00-10:00, 10:30-15:30, 16:00-17:00

    # Days to check: Monday (only after 14:30) and Tuesday (all day)
    days = [
        ("Monday", 330, 480, ryan_monday + adam_monday),  # 14:30 = 330 minutes from 9:00
        ("Tuesday", 0, 480, ryan_tuesday + adam_tuesday)
    ]

    for day, window_start, window_end, intervals in days:
        # Merge overlapping busy intervals
        intervals.sort(key=lambda x: x[0])
        merged = []
        for start, end in intervals:
            if not merged:
                merged.append((start, end))
            else:
                last_start, last_end = merged[-1]
                if start <= last_end:
                    merged[-1] = (last_start, max(last_end, end))
                else:
                    merged.append((start, end))
        
        # Compute free intervals within the window
        free = []
        current = window_start
        for start, end in merged:
            if end <= window_start:
                continue
            if start > window_end:
                break
            if start > current:
                free.append((current, start))
                current = end
            else:
                if end > current:
                    current = end
        if current < window_end:
            free.append((current, window_end))
        
        # Find the first free interval with at least 30 minutes
        for start, end in free:
            if end - start >= 30:
                meeting_start = start
                meeting_end = meeting_start + 30
                start_str = min_to_time(meeting_start)
                end_str = min_to_time(meeting_end)
                print(day)
                print(f"{start_str}:{end_str}")
                return

if __name__ == "__main__":
    main()