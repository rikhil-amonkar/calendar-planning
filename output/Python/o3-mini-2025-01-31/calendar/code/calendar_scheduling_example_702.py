from datetime import datetime, timedelta

# Helper function: convert time string "HH:MM" to minutes since midnight.
def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

# Helper function: convert minutes since midnight back to "HH:MM" format.
def minutes_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Meeting duration in minutes
MEETING_DURATION = 30

# Workday boundaries (9:00 to 17:00) in minutes since midnight.
WORK_START = time_to_minutes("09:00")
WORK_END = time_to_minutes("17:00")

# Busy schedules per participant per day.
# Times are given as (start, end) in HH:MM.
schedules = {
    "Robert": {
        "Monday": [("11:00", "11:30"), ("14:00", "14:30"), ("15:30", "16:00")],
        "Tuesday": [("10:30", "11:00"), ("15:00", "15:30")],
        "Wednesday": [("10:00", "11:00"), ("11:30", "12:00"),
                      ("12:30", "13:00"), ("13:30", "14:00"),
                      ("15:00", "15:30"), ("16:00", "16:30")]
    },
    "Ralph": {
        "Monday": [("10:00", "13:30"), ("14:00", "14:30"), ("15:00", "17:00")],
        "Tuesday": [("9:00", "9:30"), ("10:00", "10:30"), 
                    ("11:00", "11:30"), ("12:00", "13:00"),
                    ("14:00", "15:30"), ("16:00", "17:00")],
        "Wednesday": [("10:30", "11:00"), ("11:30", "12:00"), 
                      ("13:00", "14:30"), ("16:30", "17:00")]
    }
}

# Define the days available for scheduling
# Robert would like to avoid more meetings on Monday if possible.
# So we order by preference: Tuesday, Wednesday, then Monday.
preferred_days = ["Tuesday", "Wednesday", "Monday"]

# Merge busy intervals for a given day from all participants and merge overlapping intervals.
def merge_intervals(intervals):
    if not intervals:
        return []
    # sort intervals by start time (in minutes)
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for current in intervals[1:]:
        last = merged[-1]
        # if current interval starts before or exactly when the last one ends, merge them
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

# Find a free time slot on a particular day given the merged busy intervals
def find_free_slot(busy_intervals):
    free_slots = []
    # Check interval between work start and first busy interval
    if busy_intervals:
        if WORK_START < busy_intervals[0][0]:
            free_slots.append((WORK_START, busy_intervals[0][0]))
    else:
        free_slots.append((WORK_START, WORK_END))
    # Check between busy intervals
    for i in range(len(busy_intervals) - 1):
        end_current = busy_intervals[i][1]
        start_next = busy_intervals[i+1][0]
        if start_next - end_current >= MEETING_DURATION:
            free_slots.append((end_current, start_next))
    # Check interval between last busy interval and work end
    if busy_intervals:
        if WORK_END > busy_intervals[-1][1]:
            free_slots.append((busy_intervals[-1][1], WORK_END))
    # Look for the earliest free slot that satisfies the meeting duration
    for start, end in free_slots:
        if end - start >= MEETING_DURATION:
            return start, start + MEETING_DURATION
    return None

# Main scheduling function. It will check days in the preferred order.
def schedule_meeting():
    for day in preferred_days:
        all_busy = []
        for person in schedules:
            # Get busy intervals for this day, if any.
            intervals = schedules[person].get(day, [])
            for start_str, end_str in intervals:
                start = time_to_minutes(start_str)
                end   = time_to_minutes(end_str)
                # Only consider intervals that fall within work hours.
                # They should, but we'll clip them if needed.
                start = max(start, WORK_START)
                end   = min(end, WORK_END)
                if start < end:
                    all_busy.append((start, end))
        # Merge all busy intervals for the day.
        merged_busy = merge_intervals(all_busy)
        slot = find_free_slot(merged_busy)
        if slot:
            meeting_start, meeting_end = slot
            # Format the meeting time as required: HH:MM:HH:MM and output the day.
            meeting_time = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
            print(f"{day} {meeting_time}")
            return
    print("No available slot found.")

if __name__ == "__main__":
    schedule_meeting()