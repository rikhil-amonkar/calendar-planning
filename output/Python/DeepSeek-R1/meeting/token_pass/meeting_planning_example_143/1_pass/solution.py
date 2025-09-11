import json

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes
    travel_times = {
        ('North Beach', 'Pacific Heights'): 8,
        ('North Beach', 'Embarcadero'): 6,
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Embarcadero'): 10,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Pacific Heights'): 11
    }
    
    # Constraints
    start_location = "North Beach"
    start_time = "9:00"
    karen_location = "Pacific Heights"
    karen_start = "18:45"
    karen_end = "20:15"
    karen_min_duration = 90
    mark_location = "Embarcadero"
    mark_start = "13:00"
    mark_end = "17:45"
    mark_min_duration = 120
    
    # Convert times to minutes
    start_min = time_to_minutes(start_time)
    karen_start_min = time_to_minutes(karen_start)
    karen_end_min = time_to_minutes(karen_end)
    mark_start_min = time_to_minutes(mark_start)
    mark_end_min = time_to_minutes(mark_end)
    
    # Calculate latest possible Mark meeting end time
    mark_meet_end = mark_end_min
    mark_meet_start = mark_meet_end - mark_min_duration
    if mark_meet_start < mark_start_min:
        mark_meet_start = mark_start_min
        mark_meet_end = mark_meet_start + mark_min_duration
        if mark_meet_end > mark_end_min:
            mark_meet_end = mark_end_min
    
    # Travel from Mark to Karen
    travel_to_karen = travel_times[(mark_location, karen_location)]
    arrival_at_karen = mark_meet_end + travel_to_karen
    
    # Calculate Karen meeting time
    karen_meet_start = max(arrival_at_karen, karen_start_min)
    karen_meet_end = karen_meet_start + karen_min_duration
    if karen_meet_end > karen_end_min:
        karen_meet_end = karen_end_min
        karen_meet_start = karen_meet_end - karen_min_duration
        if karen_meet_start < karen_start_min:
            karen_meet_start = karen_start_min
    
    # Convert back to time strings
    mark_start_str = minutes_to_time(mark_meet_start)
    mark_end_str = minutes_to_time(mark_meet_end)
    karen_start_str = minutes_to_time(karen_meet_start)
    karen_end_str = minutes_to_time(karen_meet_end)
    
    # Create itinerary
    itinerary = [
        {
            "action": "meet",
            "location": mark_location,
            "person": "Mark",
            "start_time": mark_start_str,
            "end_time": mark_end_str
        },
        {
            "action": "meet",
            "location": karen_location,
            "person": "Karen",
            "start_time": karen_start_str,
            "end_time": karen_end_str
        }
    ]
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()