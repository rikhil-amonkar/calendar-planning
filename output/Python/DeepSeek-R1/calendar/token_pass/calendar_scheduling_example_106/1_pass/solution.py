def main():
    # Define work hours in minutes (9:00 to 17:00)
    work_start = 9 * 60
    work_end = 17 * 60
    meeting_duration = 60

    # Busy intervals for each participant in minutes since start of day
    olivia_busy = [(12*60 + 30, 13*60 + 30), (14*60 + 30, 15*60 + 0), (16*60 + 30, 17*60 + 0)]
    anna_busy = []  # No meetings
    virginia_busy = [(9*60 + 0, 10*60 + 0), (11*60 + 30, 16*60 + 0), (16*60 + 30, 17*60 + 0)]
    paul_busy = [(9*60 + 0, 9*60 + 30), (11*60 + 0, 11*60 + 30), (13*60 + 0, 14*60 + 0), (14*60 + 30, 16*60 + 0), (16*60 + 30, 17*60 + 0)]

    # Combine all busy intervals
    all_busy = olivia_busy + anna_busy + virginia_busy + paul_busy

    # Merge overlapping busy intervals
    all_busy.sort(key=lambda x: x[0])
    merged = []
    current_start, current_end = all_busy[0]
    for start, end in all_busy[1:]:
        if start <= current_end:
            current_end = max(current_end, end)
        else:
            merged.append((current_start, current_end))
            current_start, current_end = start, end
    merged.append((current_start, current_end))

    # Check for available slots between work hours
    # Check before first meeting
    if merged[0][0] - work_start >= meeting_duration:
        slot_start = work_start
        slot_end = slot_start + meeting_duration
        print_time_slot(slot_start, slot_end, "Monday")
        return

    # Check between meetings
    for i in range(len(merged) - 1):
        gap_start = merged[i][1]
        gap_end = merged[i+1][0]
        if gap_end - gap_start >= meeting_duration:
            slot_start = gap_start
            slot_end = slot_start + meeting_duration
            print_time_slot(slot_start, slot_end, "Monday")
            return

    # Check after last meeting
    if work_end - merged[-1][1] >= meeting_duration:
        slot_start = merged[-1][1]
        slot_end = slot_start + meeting_duration
        print_time_slot(slot_start, slot_end, "Monday")
        return

def print_time_slot(start_minutes, end_minutes, day):
    start_hour = start_minutes // 60
    start_minute = start_minutes % 60
    end_hour = end_minutes // 60
    end_minute = end_minutes % 60
    print(f"{day}:{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")

if __name__ == "__main__":
    main()