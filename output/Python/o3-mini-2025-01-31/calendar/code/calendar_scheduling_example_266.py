from datetime import datetime, timedelta

def time_to_minutes(time_str):
    # Expects time in "HH:MM" format.
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    return f"{minutes//60:02d}:{minutes%60:02d}"

# Workday start and end (in minutes from midnight)
WORKDAY_START = time_to_minutes("09:00")
WORKDAY_END = time_to_minutes("17:00")
MEETING_DURATION = 30  # minutes

# Busy schedules for each participant on Monday
# Each entry is a tuple (start, end) in minutes
busy_schedules = {
    "Joe": [(time_to_minutes("09:30"), time_to_minutes("10:00")),
            (time_to_minutes("10:30"), time_to_minutes("11:00"))],
    
    "Keith": [(time_to_minutes("11:30"), time_to_minutes("12:00")),
              (time_to_minutes("15:00"), time_to_minutes("15:30"))],
    
    "Patricia": [(time_to_minutes("09:00"), time_to_minutes("09:30")),
                 (time_to_minutes("13:00"), time_to_minutes("13:30"))],
    
    "Nancy": [(time_to_minutes("09:00"), time_to_minutes("11:00")),
              (time_to_minutes("11:30"), time_to_minutes("16:30"))],
    
    "Pamela": [(time_to_minutes("09:00"), time_to_minutes("10:00")),
               (time_to_minutes("10:30"), time_to_minutes("11:00")),
               (time_to_minutes("11:30"), time_to_minutes("12:30")),
               (time_to_minutes("13:00"), time_to_minutes("14:00")),
               (time_to_minutes("14:30"), time_to_minutes("15:00")),
               (time_to_minutes("15:30"), time_to_minutes("16:00")),
               (time_to_minutes("16:30"), time_to_minutes("17:00"))]
}

def merge_intervals(intervals):
    # Sort intervals by start time
    intervals = sorted(intervals, key=lambda x: x[0])
    merged = []
    for current in intervals:
        if not merged or current[0] > merged[-1][1]:
            merged.append(list(current))
        else:
            merged[-1][1] = max(merged[-1][1], current[1])
    return merged

def get_common_free_time(busy):
    # Merge all busy intervals from all participants
    all_busy = []
    for intervals in busy.values():
        all_busy.extend(intervals)
    merged_busy = merge_intervals(all_busy)
    
    free_intervals = []
    # From workday start to first busy interval
    if merged_busy:
        if WORKDAY_START < merged_busy[0][0]:
            free_intervals.append((WORKDAY_START, merged_busy[0][0]))
        # Between busy intervals
        for i in range(len(merged_busy) - 1):
            start = merged_busy[i][1]
            end = merged_busy[i+1][0]
            if start < end:
                free_intervals.append((start, end))
        # After last busy interval until end of workday
        if merged_busy[-1][1] < WORKDAY_END:
            free_intervals.append((merged_busy[-1][1], WORKDAY_END))
    else:
        free_intervals.append((WORKDAY_START, WORKDAY_END))
    return free_intervals

def find_meeting_slot(free_intervals, duration):
    for start, end in free_intervals:
        if end - start >= duration:
            return start, start + duration
    return None

def main():
    day = "Monday"
    free_intervals = get_common_free_time(busy_schedules)
    slot = find_meeting_slot(free_intervals, MEETING_DURATION)
    if slot:
        start_time = minutes_to_time(slot[0])
        end_time = minutes_to_time(slot[1])
        # Format the output as HH:MM:HH:MM and include the day of the week.
        print(f"{start_time}:{end_time}")
        print(day)
    else:
        print("No available slot found.")

if __name__ == '__main__':
    main()