def main():
    work_start = 0  # 9:00 in minutes from 9:00
    work_end = 480   # 17:00
    eric_busy = [(180, 240), (300, 360)]
    henry_busy = [(30, 60), (90, 120), (150, 210), (240, 270), (330, 360), (420, 480)]

    def get_free_intervals(busy_intervals, start_time, end_time):
        if not busy_intervals:
            return [(start_time, end_time)]
        sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
        free = []
        current = start_time
        for s, e in sorted_busy:
            if current < s:
                free.append((current, s))
            current = e
        if current < end_time:
            free.append((current, end_time))
        return free

    free_eric = get_free_intervals(eric_busy, work_start, work_end)
    free_henry = get_free_intervals(henry_busy, work_start, work_end)

    candidate_slots = []
    for e_int in free_eric:
        for h_int in free_henry:
            start_over = max(e_int[0], h_int[0])
            end_over = min(e_int[1], h_int[1])
            if start_over < end_over and (end_over - start_over) >= 30:
                candidate_slots.append((start_over, end_over))

    candidate_meetings = []
    for s, e in candidate_slots:
        meeting_end = s + 30
        candidate_meetings.append((s, meeting_end))

    preferred_meetings = [meeting for meeting in candidate_meetings if meeting[1] <= 60]

    if preferred_meetings:
        chosen_meeting = min(preferred_meetings, key=lambda x: x[0])
    else:
        chosen_meeting = min(candidate_meetings, key=lambda x: x[0])

    def format_time(minutes):
        total_minutes = minutes
        hours = 9 + total_minutes // 60
        minutes_part = total_minutes % 60
        return f"{hours:02d}:{minutes_part:02d}"

    start_str = format_time(chosen_meeting[0])
    end_str = format_time(chosen_meeting[1])
    time_range_str = f"{start_str}:{end_str}"

    print("Monday")
    print(time_range_str)

if __name__ == "__main__":
    main()