from datetime import datetime, timedelta

def parse_time(time_str):
    """Convert 'HH:MM' to minutes since midnight."""
    return datetime.strptime(time_str, "%H:%M")

def time_range(start_str, end_str):
    """Return tuple of datetime objects for start and end."""
    return parse_time(start_str), parse_time(end_str)

def blocked_to_free(blocked, day_start, day_end):
    """Convert blocked intervals to free intervals within work hours."""
    free = []
    current = day_start
    for block_start, block_end in sorted(blocked):
        if current < block_start:
            free.append((current, block_start))
        current = max(current, block_end)
    if current < day_end:
        free.append((current, day_end))
    return free

def intersect_free_slots(slots1, slots2):
    """Intersect two lists of free time slots."""
    intersections = []
    i = j = 0
    while i < len(slots1) and j < len(slots2):
        start = max(slots1[i][0], slots2[j][0])
        end = min(slots1[i][1], slots2[j][1])
        if start < end:
            intersections.append((start, end))
        if slots1[i][1] < slots2[j][1]:
            i += 1
        else:
            j += 1
    return intersections

def main():
    work_start = parse_time("09:00")
    work_end = parse_time("17:00")
    meeting_duration = timedelta(minutes=30)
    
    # Margaret's blocked times (as datetime ranges)
    margaret_blocked = {
        "Monday": [
            time_range("10:30", "11:00"),
            time_range("11:30", "12:00"),
            time_range("13:00", "13:30"),
            time_range("15:00", "17:00"),
        ],
        "Tuesday": [
            time_range("12:00", "12:30"),
        ],
    }
    
    # Alexis's blocked times
    alexis_blocked = {
        "Monday": [
            time_range("09:30", "11:30"),
            time_range("12:30", "13:00"),
            time_range("14:00", "17:00"),
        ],
        "Tuesday": [
            time_range("09:00", "09:30"),
            time_range("10:00", "10:30"),
            time_range("14:00", "16:30"),
        ],
    }
    
    days = ["Monday", "Tuesday"]
    
    # Margaret's preferences: not Monday, not Tuesday before 14:30
    # So only consider Tuesday from 14:30 onward for Margaret
    margaret_pref_adjust = {
        "Monday": [time_range("00:00", "23:59")],  # effectively blocked all Monday
        "Tuesday": [time_range("00:00", "14:30")], # blocked before 14:30
    }
    
    # Combine Margaret's blocked times with preference blocks
    margaret_total_blocked = {day: [] for day in days}
    for day in days:
        margaret_total_blocked[day] = sorted(
            margaret_blocked.get(day, []) + margaret_pref_adjust.get(day, []),
            key=lambda x: x[0]
        )
    
    # Find free slots for each person
    free_slots = {day: {} for day in days}
    for day in days:
        # Margaret's free slots
        margaret_free = blocked_to_free(margaret_total_blocked[day], work_start, work_end)
        # Alexis's free slots
        alexis_free = blocked_to_free(alexis_blocked.get(day, []), work_start, work_end)
        # Intersect
        free_slots[day]["Margaret"] = margaret_free
        free_slots[day]["Alexis"] = alexis_free
        free_slots[day]["Intersection"] = intersect_free_slots(margaret_free, alexis_free)
    
    # Find first slot that fits meeting duration
    meeting_slot = None
    meeting_day = None
    for day in days:
        for slot_start, slot_end in free_slots[day]["Intersection"]:
            if slot_end - slot_start >= meeting_duration:
                meeting_slot = (slot_start, slot_start + meeting_duration)
                meeting_day = day
                break
        if meeting_slot:
            break
    
    if meeting_slot:
        start_str = meeting_slot[0].strftime("%H:%M")
        end_str = meeting_slot[1].strftime("%H:%M")
        print(f"{meeting_day}:{start_str}:{end_str}")
    else:
        print("No suitable slot found")

if __name__ == "__main__":
    main()