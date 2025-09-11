def main():
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Define blocked intervals in minutes since midnight
    blocked_shirley = {
        'Monday': [(10*60+30, 11*60), (12*60, 12*60+30), (16*60, 16*60+30)],
        'Tuesday': [(9*60+30, 10*60)]
    }
    blocked_albert = {
        'Monday': [(9*60, 17*60)],  # Entire Monday blocked
        'Tuesday': [(9*60+30, 11*60), (11*60+30, 12*60+30), (13*60, 16*60), (16*60+30, 17*60)]
    }

    days = ['Monday', 'Tuesday']
    candidate = None

    for day in days:
        # Compute free intervals for Shirley
        shirley_free = []
        current = work_start
        for block in sorted(blocked_shirley[day]):
            if current < block[0]:
                shirley_free.append((current, block[0]))
            current = block[1]
        if current < work_end:
            shirley_free.append((current, work_end))

        # Compute free intervals for Albert
        albert_free = []
        current = work_start
        for block in sorted(blocked_albert[day]):
            if current < block[0]:
                albert_free.append((current, block[0]))
            current = block[1]
        if current < work_end:
            albert_free.append((current, work_end))

        # Check for overlapping free intervals of at least meeting_duration
        for a_start, a_end in albert_free:
            if a_end - a_start < meeting_duration:
                continue
            for s_start, s_end in shirley_free:
                if a_start >= s_start and a_end <= s_end:
                    candidate = (day, a_start, a_end)
                    break
            if candidate:
                break
        if candidate:
            break

    if candidate:
        day, start_min, end_min = candidate
        # Convert minutes to HH:MM format
        start_time = f"{start_min // 60:02d}:{start_min % 60:02d}"
        end_time = f"{end_min // 60:02d}:{end_min % 60:02d}"
        print(f"{day} {start_time}:{end_time}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()