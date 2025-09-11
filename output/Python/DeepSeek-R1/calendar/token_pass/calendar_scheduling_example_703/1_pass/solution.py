def main():
    # Define work hours (9:00 to 17:00) in minutes
    work_start = 9 * 60
    work_end = 17 * 60

    # Define days to check in order of preference (Tuesday, Wednesday, Monday)
    days = ["Tuesday", "Wednesday", "Monday"]

    # Define busy intervals for each participant per day (in minutes from midnight)
    stephanie_busy = {
        "Monday": [(9*60+30, 10*60), (10*60+30, 11*60), (11*60+30, 12*60), (14*60, 14*60+30)],
        "Tuesday": [(12*60, 13*60)],
        "Wednesday": [(9*60, 10*60), (13*60, 14*60)]
    }

    betty_busy = {
        "Monday": [(9*60, 10*60), (11*60, 11*60+30), (14*60+30, 15*60), (15*60+30, 16*60)],
        "Tuesday": [(9*60, 9*60+30), (11*60+30, 12*60), (12*60+30, 14*60+30), (15*60+30, 16*60)],
        "Wednesday": [(10*60, 11*60+30), (12*60, 14*60), (14*60+30, 17*60)]
    }

    # Function to compute free intervals given busy intervals and work hours
    def get_free_intervals(busy_list, day_start, day_end):
        busy_list.sort(key=lambda x: x[0])
        free_intervals = []
        current = day_start
        for start, end in busy_list:
            if current < start:
                free_intervals.append((current, start))
            current = max(current, end)
        if current < day_end:
            free_intervals.append((current, day_end))
        return free_intervals

    # Function to adjust Betty's Tuesday intervals (cannot meet after 12:30)
    def adjust_betty_tuesday(intervals):
        adjusted = []
        cutoff = 12 * 60 + 30  # 12:30 in minutes
        for start, end in intervals:
            if end <= cutoff:
                adjusted.append((start, end))
            elif start < cutoff:
                adjusted.append((start, cutoff))
        return adjusted

    # Convert minutes to HH:MM string
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    # Find first available 1-hour slot
    for day in days:
        # Get free intervals for Stephanie
        steph_free = get_free_intervals(stephanie_busy.get(day, []), work_start, work_end)
        
        # Get free intervals for Betty
        betty_free = get_free_intervals(betty_busy.get(day, []), work_start, work_end)
        
        # Adjust Betty's free intervals for Tuesday
        if day == "Tuesday":
            betty_free = adjust_betty_tuesday(betty_free)
        
        # Find overlapping free intervals
        for s_start, s_end in steph_free:
            for b_start, b_end in betty_free:
                overlap_start = max(s_start, b_start)
                overlap_end = min(s_end, b_end)
                if overlap_end - overlap_start >= 60:  # 1 hour meeting
                    meeting_start = overlap_start
                    meeting_end = meeting_start + 60
                    time_str = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
                    print(f"{day} {time_str}")
                    return

    # Fallback to Monday if no other found (though problem states solution exists)
    monday_steph_free = get_free_intervals(stephanie_busy["Monday"], work_start, work_end)
    monday_betty_free = get_free_intervals(betty_busy["Monday"], work_start, work_end)
    for s_start, s_end in monday_steph_free:
        for b_start, b_end in monday_betty_free:
            overlap_start = max(s_start, b_start)
            overlap_end = min(s_end, b_end)
            if overlap_end - overlap_start >= 60:
                meeting_start = overlap_start
                meeting_end = meeting_start + 60
                time_str = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
                print(f"Monday {time_str}")
                return

if __name__ == "__main__":
    main()