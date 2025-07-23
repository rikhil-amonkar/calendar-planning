def find_meeting_time(participants_schedules, days, work_hours_start, work_hours_end, duration_minutes):
    # Convert work hours to minutes since midnight for easier comparison
    work_start = work_hours_start * 60
    work_end = work_hours_end * 60
    
    for day in days:
        # Collect all busy intervals for the day for all participants
        busy_intervals = []
        for participant in participants_schedules:
            if day in participant:
                busy_intervals.extend(participant[day])
        
        # Merge overlapping or adjacent busy intervals
        if not busy_intervals:
            # No busy intervals, the whole work day is free
            start_time = work_start
            end_time = work_end
            if end_time - start_time >= duration_minutes:
                return day, (start_time, start_time + duration_minutes)
            else:
                continue
        
        # Sort busy intervals by start time
        busy_intervals.sort()
        
        merged = []
        for interval in busy_intervals:
            if not merged:
                merged.append(interval)
            else:
                last_start, last_end = merged[-1]
                current_start, current_end = interval
                if current_start <= last_end:
                    # Overlapping or adjacent, merge them
                    new_start = last_start
                    new_end = max(last_end, current_end)
                    merged[-1] = (new_start, new_end)
                else:
                    merged.append(interval)
        
        # Check the time before the first busy interval
        first_start, first_end = merged[0]
        if first_start - work_start >= duration_minutes:
            return day, (work_start, work_start + duration_minutes)
        
        # Check the time between busy intervals
        for i in range(1, len(merged)):
            prev_start, prev_end = merged[i-1]
            current_start, current_end = merged[i]
            if current_start - prev_end >= duration_minutes:
                return day, (prev_end, prev_end + duration_minutes)
        
        # Check the time after the last busy interval
        last_start, last_end = merged[-1]
        if work_end - last_end >= duration_minutes:
            return day, (last_end, last_end + duration_minutes)
    
    return None, None

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define participants' schedules
mary_schedule = {
    "Tuesday": [(10*60, 10*60+30), (15*60+30, 16*60)],
    "Wednesday": [(9*60+30, 10*60), (15*60, 15*60+30)],
    "Thursday": [(9*60, 10*60), (10*60+30, 11*60+30)],
}

alexis_schedule = {
    "Monday": [(9*60, 10*60), (10*60+30, 12*60), (12*60+30, 16*60+30)],
    "Tuesday": [(9*60, 10*60), (10*60+30, 11*60+30), (12*60, 15*60+30), (16*60, 17*60)],
    "Wednesday": [(9*60, 11*60), (11*60+30, 17*60)],
    "Thursday": [(10*60, 12*60), (14*60, 14*60+30), (15*60+30, 16*60), (16*60+30, 17*60)],
}

# Define parameters
days_to_check = ["Monday", "Tuesday", "Wednesday", "Thursday"]
work_hours_start = 9
work_hours_end = 17
meeting_duration = 30

# Find the earliest meeting time
day, (start_min, end_min) = find_meeting_time([mary_schedule, alexis_schedule], days_to_check, work_hours_start, work_hours_end, meeting_duration)

# Format the output
start_time = minutes_to_time(start_min)
end_time = minutes_to_time(end_min)
print(f"{day}: {start_time}:{end_time}")