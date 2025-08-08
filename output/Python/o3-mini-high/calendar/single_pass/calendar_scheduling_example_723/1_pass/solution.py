def minutes_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def subtract_busy(work_start, work_end, busy):
    free = []
    current = work_start
    for start, end in sorted(busy):
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(list1, list2):
    intersections = []
    i, j = 0, 0
    while i < len(list1) and j < len(list2):
        start1, end1 = list1[i]
        start2, end2 = list2[j]
        start = max(start1, start2)
        end = min(end1, end2)
        if start < end:
            intersections.append((start, end))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

def find_slot(free1, free2, duration):
    for start1, end1 in intersect_intervals(free1, free2):
        if end1 - start1 >= duration:
            return start1, start1 + duration
    return None

# Define work hours and meeting duration in minutes
WORK_START = 9 * 60   # 09:00 in minutes
WORK_END   = 17 * 60  # 17:00 in minutes
MEETING_DURATION = 30

# Arthur's busy slots (in minutes)
arthur_busy = {
    "Monday": [(11*60, 11*60+30), (13*60+30, 14*60), (15*60, 15*60+30)],
    "Tuesday": [(13*60, 13*60+30), (16*60, 16*60+30)],
    "Wednesday": [(10*60, 10*60+30), (11*60, 11*60+30),
                  (12*60, 12*60+30), (14*60, 14*60+30), (16*60, 16*60+30)]
}

# Michael's busy slots (in minutes)
michael_busy = {
    "Monday": [(9*60, 12*60), (12*60+30, 13*60), (14*60, 14*60+30), (15*60, 17*60)],
    "Tuesday": [(9*60+30, 11*60+30), (12*60, 13*60+30), (14*60, 15*60+30)],
    "Wednesday": [(10*60, 12*60+30), (13*60, 13*60+30)]
}

# Arthur cannot meet on Tuesday
days = ["Monday", "Tuesday", "Wednesday"]
meeting_day = None
meeting_time = None

for day in days:
    if day == "Tuesday":
        continue  # skip Tuesday for Arthur

    arthur_free = subtract_busy(WORK_START, WORK_END, arthur_busy.get(day, []))
    michael_free = subtract_busy(WORK_START, WORK_END, michael_busy.get(day, []))
    
    slot = find_slot(arthur_free, michael_free, MEETING_DURATION)
    if slot:
        meeting_day = day
        meeting_time = slot
        break

if meeting_day and meeting_time:
    start_str = minutes_to_str(meeting_time[0])
    end_str = minutes_to_str(meeting_time[1])
    # Output format: Day {HH:MM:HH:MM}
    print(f"{meeting_day} {start_str}:{end_str}")
else:
    print("No available meeting slot found.")