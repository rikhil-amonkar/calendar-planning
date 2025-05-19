from datetime import datetime, timedelta

# Define working hours in minutes (9:00 -> 540, 17:00 -> 1020)
WORK_START = 9 * 60      # 540
WORK_END = 17 * 60       # 1020
MEETING_DURATION = 30    # minutes

# Define the schedules in minutes past midnight for each day.
# Each participant schedule is a dictionary where key is the day and value is a list of (start, end) busy intervals.
# Times are converted to minutes, e.g., 10:30 -> 10*60+30 = 630.
def time_to_minutes(time_str):
    """Convert HH:MM string to minutes since midnight."""
    t = datetime.strptime(time_str, "%H:%M")
    return t.hour * 60 + t.minute

schedules = {
    "Ronald": {
        "Monday": [(time_to_minutes("10:30"), time_to_minutes("11:00")),
                   (time_to_minutes("12:00"), time_to_minutes("12:30")),
                   (time_to_minutes("15:30"), time_to_minutes("16:00"))],
        "Tuesday": [(time_to_minutes("9:00"), time_to_minutes("9:30")),
                    (time_to_minutes("12:00"), time_to_minutes("12:30")),
                    (time_to_minutes("15:30"), time_to_minutes("16:30"))],
        "Wednesday": [(time_to_minutes("9:30"), time_to_minutes("10:30")),
                      (time_to_minutes("11:00"), time_to_minutes("12:00")),
                      (time_to_minutes("12:30"), time_to_minutes("13:00")),
                      (time_to_minutes("13:30"), time_to_minutes("14:00")),
                      (time_to_minutes("16:30"), time_to_minutes("17:00"))]
    },
    "Amber": {
        "Monday": [(time_to_minutes("9:00"), time_to_minutes("9:30")),
                   (time_to_minutes("10:00"), time_to_minutes("10:30")),
                   (time_to_minutes("11:30"), time_to_minutes("12:00")),
                   (time_to_minutes("12:30"), time_to_minutes("14:00")),
                   (time_to_minutes("14:30"), time_to_minutes("15:00")),
                   (time_to_minutes("15:30"), time_to_minutes("17:00"))],
        "Tuesday": [(time_to_minutes("9:00"), time_to_minutes("9:30")),
                    (time_to_minutes("10:00"), time_to_minutes("11:30")),
                    (time_to_minutes("12:00"), time_to_minutes("12:30")),
                    (time_to_minutes("13:30"), time_to_minutes("15:30")),
                    (time_to_minutes("16:30"), time_to_minutes("17:00"))],
        "Wednesday": [(time_to_minutes("9:00"), time_to_minutes("9:30")),
                      (time_to_minutes("10:00"), time_to_minutes("10:30")),
                      (time_to_minutes("11:00"), time_to_minutes("13:30")),
                      (time_to_minutes("15:00"), time_to_minutes("15:30"))]
    }
}

# List of days in order.
days = ["Monday", "Tuesday", "Wednesday"]

def merge_intervals(intervals):
    """Merge overlapping intervals."""
    if not intervals:
        return []
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for current in intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def find_free_slot(merged_intervals):
    """Find the earliest free slot of meeting duration in working hours given merged busy intervals."""
    # Check gap from WORK_START to first busy interval start
    prev_end = WORK_START
    for interval in merged_intervals:
        start, end = interval
        if start - prev_end >= MEETING_DURATION:
            return prev_end, prev_end + MEETING_DURATION
        prev_end = max(prev_end, end)
    # Check gap after the last busy interval until WORK_END
    if WORK_END - prev_end >= MEETING_DURATION:
        return prev_end, prev_end + MEETING_DURATION
    return None

def minutes_to_time(minutes):
    """Convert minutes since midnight to HH:MM string."""
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def schedule_meeting():
    for day in days:
        # Gather all busy intervals for this day across participants
        busy = []
        for person in schedules:
            busy.extend(schedules[person].get(day, []))
        # Merge overlapping busy intervals
        merged_busy = merge_intervals(busy)
        # Find an available free slot on this day
        slot = find_free_slot(merged_busy)
        if slot:
            start, end = slot
            start_time = minutes_to_time(start)
            end_time = minutes_to_time(end)
            print(f"{day} {start_time}:{end_time}")
            return
    print("No available meeting slot found.")

if __name__ == "__main__":
    schedule_meeting()