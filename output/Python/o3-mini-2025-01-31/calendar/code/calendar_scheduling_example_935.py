from datetime import datetime, timedelta

# Define meeting duration in minutes
MEETING_DURATION = 30

# Define working hours (in minutes since midnight)
WORK_START = 9 * 60    # 9:00 in minutes
WORK_END = 17 * 60     # 17:00 in minutes

# Weekly schedule for each participant.
# Times are expressed in minutes since midnight.
schedules = {
    "Terry": {
        "Monday": [(10*60+30, 11*60), (12*60+30, 14*60), (15*60, 17*60)],
        "Tuesday": [(9*60+30, 10*60), (10*60+30, 11*60), (14*60, 14*60+30), (16*60, 16*60+30)],
        "Wednesday": [(9*60+30, 10*60+30), (11*60, 12*60), (13*60, 13*60+30), (15*60, 16*60), (16*60+30, 17*60)],
        "Thursday": [(9*60+30, 10*60), (12*60, 12*60+30), (13*60, 14*60+30), (16*60, 16*60+30)],
        "Friday": [(9*60, 11*60+30), (12*60, 12*60+30), (13*60+30, 16*60), (16*60+30, 17*60)],
    },
    "Frances": {
        "Monday": [(9*60+30, 11*60), (11*60+30, 13*60), (14*60, 14*60+30), (15*60, 16*60)],
        "Tuesday": [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 12*60), (13*60, 14*60+30), (15*60+30, 16*60+30)],
        "Wednesday": [(9*60+30, 10*60), (10*60+30, 11*60), (11*60+30, 16*60), (16*60+30, 17*60)],
        "Thursday": [(11*60, 12*60+30), (14*60+30, 17*60)],
        "Friday": [(9*60+30, 10*60+30), (11*60, 12*60+30), (13*60, 16*60), (16*60+30, 17*60)],
    }
}

# The days order.
# Frances prefers to avoid Tuesday, so we check Monday, Wednesday, Thursday, Friday first and then Tuesday.
days_order = ["Monday", "Wednesday", "Thursday", "Friday", "Tuesday"]

def merge_intervals(intervals):
    """Merge overlapping intervals."""
    if not intervals:
        return []
    intervals.sort()
    merged = [intervals[0]]
    for current in intervals[1:]:
        prev = merged[-1]
        # if the current interval overlaps with the previous one, merge them
        if current[0] <= prev[1]:
            merged[-1] = (prev[0], max(prev[1], current[1]))
        else:
            merged.append(current)
    return merged

def find_free_slot(busy_intervals):
    """Given busy intervals, find the earliest free slot within working hours."""
    # Start with the beginning of working hours.
    start = WORK_START
    
    # Check free time before first busy interval.
    for b_start, b_end in busy_intervals:
        if start + MEETING_DURATION <= b_start:
            # Found free slot
            return start, start + MEETING_DURATION
        # Move start to the later of current start and busy end
        start = max(start, b_end)
    
    # After all busy intervals, check if there's enough time before work end.
    if start + MEETING_DURATION <= WORK_END:
        return start, start + MEETING_DURATION
    
    return None

def minutes_to_HHMM(minutes):
    hrs = minutes // 60
    mins = minutes % 60
    return f"{hrs:02d}:{mins:02d}"

# Main scheduling logic:
def schedule_meeting():
    for day in days_order:
        combined_busy = []
        # Combine busy intervals for both participants for the given day.
        for person in schedules:
            intervals = schedules[person].get(day, [])
            combined_busy.extend(intervals)
        
        # Merge intervals for a clear picture of busy times.
        merged_busy = merge_intervals(combined_busy)
        
        slot = find_free_slot(merged_busy)
        if slot:
            start, end = slot
            start_str = minutes_to_HHMM(start)
            end_str = minutes_to_HHMM(end)
            return day, f"{{{start_str}:{end_str}}}"
    
    return None

result = schedule_meeting()
if result:
    day, time_range = result
    print(day, time_range)
else:
    print("No valid meeting slot found within the working hours.")

if __name__ == "__main__":
    pass