def convert_time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def convert_minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def find_meeting_time(busy_schedule, working_start, working_end, meeting_duration):
    for candidate_start in range(working_start, working_end - meeting_duration + 1):
        candidate_end = candidate_start + meeting_duration
        conflict_found = False
        for participant, intervals in busy_schedule.items():
            for interval in intervals:
                # Check for overlap: intervals are treated as [start, end)
                if candidate_start < interval[1] and candidate_end > interval[0]:
                    conflict_found = True
                    break
            if conflict_found:
                break
        if not conflict_found:
            return candidate_start, candidate_end
    return None, None

def main():
    meeting_duration = 30  # in minutes
    working_start = convert_time_to_minutes("09:00")
    working_end = convert_time_to_minutes("17:00")
    
    busy_schedule = {
        "Joan": [
            (convert_time_to_minutes("11:30"), convert_time_to_minutes("12:00")),
            (convert_time_to_minutes("14:30"), convert_time_to_minutes("15:00"))
        ],
        "Megan": [
            (convert_time_to_minutes("09:00"), convert_time_to_minutes("10:00")),
            (convert_time_to_minutes("14:00"), convert_time_to_minutes("14:30")),
            (convert_time_to_minutes("16:00"), convert_time_to_minutes("16:30"))
        ],
        "Austin": [
            # Austin is free the entire day.
        ],
        "Betty": [
            (convert_time_to_minutes("09:30"), convert_time_to_minutes("10:00")),
            (convert_time_to_minutes("11:30"), convert_time_to_minutes("12:00")),
            (convert_time_to_minutes("13:30"), convert_time_to_minutes("14:00")),
            (convert_time_to_minutes("16:00"), convert_time_to_minutes("16:30"))
        ],
        "Judith": [
            (convert_time_to_minutes("09:00"), convert_time_to_minutes("11:00")),
            (convert_time_to_minutes("12:00"), convert_time_to_minutes("13:00")),
            (convert_time_to_minutes("14:00"), convert_time_to_minutes("15:00"))
        ],
        "Terry": [
            (convert_time_to_minutes("09:30"), convert_time_to_minutes("10:00")),
            (convert_time_to_minutes("11:30"), convert_time_to_minutes("12:30")),
            (convert_time_to_minutes("13:00"), convert_time_to_minutes("14:00")),
            (convert_time_to_minutes("15:00"), convert_time_to_minutes("15:30")),
            (convert_time_to_minutes("16:00"), convert_time_to_minutes("17:00"))
        ],
        "Kathryn": [
            (convert_time_to_minutes("09:30"), convert_time_to_minutes("10:00")),
            (convert_time_to_minutes("10:30"), convert_time_to_minutes("11:00")),
            (convert_time_to_minutes("11:30"), convert_time_to_minutes("13:00")),
            (convert_time_to_minutes("14:00"), convert_time_to_minutes("16:00")),
            (convert_time_to_minutes("16:30"), convert_time_to_minutes("17:00"))
        ]
    }
    
    candidate_start, candidate_end = find_meeting_time(busy_schedule, working_start, working_end, meeting_duration)
    
    if candidate_start is not None:
        start_str = convert_minutes_to_time(candidate_start)
        end_str = convert_minutes_to_time(candidate_end)
        day = "Monday"
        print(f"{day}, {start_str}:{end_str}")
    else:
        print("No valid meeting time found.")

if __name__ == "__main__":
    main()