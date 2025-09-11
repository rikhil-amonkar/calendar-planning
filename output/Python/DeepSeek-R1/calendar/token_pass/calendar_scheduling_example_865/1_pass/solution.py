def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = [sorted_intervals[0]]
    for current in sorted_intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            last[1] = max(last[1], current[1])
        else:
            merged.append(current)
    return merged

def find_free_slots(busy_intervals, day_start, day_end):
    merged_busy = merge_intervals(busy_intervals)
    free_slots = []
    current_start = day_start
    for busy in merged_busy:
        if busy[0] > current_start:
            free_slots.append([current_start, busy[0]])
        current_start = max(current_start, busy[1])
    if current_start < day_end:
        free_slots.append([current_start, day_end])
    return free_slots

def main():
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    
    megan_schedule = {
        "Monday": [["13:00", "13:30"], ["14:00", "15:30"]],
        "Tuesday": [["9:00", "9:30"], ["12:00", "12:30"], ["16:00", "17:00"]],
        "Wednesday": [["9:30", "10:00"], ["10:30", "11:30"], ["12:30", "14:00"], ["16:00", "16:30"]],
        "Thursday": [["13:30", "14:30"], ["15:00", "15:30"]]
    }
    
    daniel_schedule = {
        "Monday": [["10:00", "11:30"], ["12:30", "15:00"]],
        "Tuesday": [["9:00", "10:00"], ["10:30", "17:00"]],
        "Wednesday": [["9:00", "10:00"], ["10:30", "11:30"], ["12:00", "17:00"]],
        "Thursday": [["9:00", "12:00"], ["12:30", "14:30"], ["15:00", "15:30"], ["16:00", "17:00"]]
    }
    
    for day in days:
        busy_intervals = []
        for person_schedule in [megan_schedule, daniel_schedule]:
            for interval in person_schedule.get(day, []):
                start_min = time_to_minutes(interval[0])
                end_min = time_to_minutes(interval[1])
                busy_intervals.append([start_min, end_min])
                
        free_slots = find_free_slots(busy_intervals, work_start, work_end)
        for slot in free_slots:
            duration = slot[1] - slot[0]
            if duration >= 60:
                meeting_start = slot[0]
                meeting_end = meeting_start + 60
                start_str = minutes_to_time(meeting_start)
                end_str = minutes_to_time(meeting_end)
                print(day)
                print(f"{start_str}:{end_str}")
                return
                
    print("No suitable time found")

if __name__ == "__main__":
    main()