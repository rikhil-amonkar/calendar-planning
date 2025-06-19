def main():
    # Define work hours in minutes from midnight (9:00 AM to 5:00 PM)
    work_start = 9 * 60  # 540 minutes
    work_end = 17 * 60   # 1020 minutes

    # Margaret is only available on Tuesday starting from 14:30 (870 minutes)
    margaret_start_tuesday = 14 * 60 + 30  # 870 minutes

    # Alexis's meetings on Tuesday: (start, end) in minutes
    alexis_meetings_tuesday = [
        (9 * 60, 9 * 60 + 30),    # 9:00-9:30 -> (540, 570)
        (10 * 60, 10 * 60 + 30),   # 10:00-10:30 -> (600, 630)
        (14 * 60, 16 * 60 + 30)    # 14:00-16:30 -> (840, 990)
    ]

    # Compute Alexis's free intervals on Tuesday within work hours
    alexis_meetings_sorted = sorted(alexis_meetings_tuesday, key=lambda x: x[0])
    alexis_free = []
    current = work_start

    for meeting in alexis_meetings_sorted:
        if current < meeting[0]:
            alexis_free.append((current, meeting[0]))
        current = max(current, meeting[1])
    if current < work_end:
        alexis_free.append((current, work_end))

    # Find an overlapping free interval with Margaret's availability (>=14:30) of at least 30 minutes
    candidate = None
    for interval in alexis_free:
        start_overlap = max(margaret_start_tuesday, interval[0])
        end_overlap = min(work_end, interval[1])
        if end_overlap - start_overlap >= 30:  # Check if duration is sufficient
            candidate = (start_overlap, start_overlap + 30)  # Schedule exactly 30 minutes
            break

    # Format the candidate time
    def format_minutes(m):
        hours = m // 60
        minutes = m % 60
        return f"{hours:02d}:{minutes:02d}"

    start_str = format_minutes(candidate[0])
    end_str = format_minutes(candidate[1])

    # Output day and time in required format (HH:MM:HH:MM)
    print("Tuesday")
    print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()