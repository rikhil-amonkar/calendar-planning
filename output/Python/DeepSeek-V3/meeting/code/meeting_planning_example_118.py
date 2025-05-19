import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

def calculate_schedule():
    # Input parameters
    arrival_time = parse_time("9:00")
    richard_available_start = parse_time("8:45")
    richard_available_end = parse_time("13:00")
    charles_available_start = parse_time("9:45")
    charles_available_end = parse_time("13:00")
    min_meet_richard = timedelta(minutes=120)
    min_meet_charles = timedelta(minutes=120)
    
    # Travel times in minutes
    travel_times = {
        ("Bayview", "Union Square"): 17,
        ("Bayview", "Presidio"): 31,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Presidio"): 24,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Union Square"): 22
    }
    
    # Possible schedules
    possible_schedules = []
    
    # Option 1: Meet Richard first, then Charles
    # Start with Richard
    travel_to_richard = timedelta(minutes=travel_times[("Bayview", "Union Square")])
    richard_start = max(arrival_time + travel_to_richard, richard_available_start)
    richard_end = richard_start + min_meet_richard
    if richard_end <= richard_available_end:
        # Then go to Charles
        travel_to_charles = timedelta(minutes=travel_times[("Union Square", "Presidio")])
        charles_start = max(richard_end + travel_to_charles, charles_available_start)
        charles_end = charles_start + min_meet_charles
        if charles_end <= charles_available_end:
            possible_schedules.append([
                {"action": "meet", "location": "Union Square", "person": "Richard", 
                 "start_time": format_time(richard_start), "end_time": format_time(richard_end)},
                {"action": "meet", "location": "Presidio", "person": "Charles", 
                 "start_time": format_time(charles_start), "end_time": format_time(charles_end)}
            ])
    
    # Option 2: Meet Charles first, then Richard
    # Start with Charles
    travel_to_charles = timedelta(minutes=travel_times[("Bayview", "Presidio")])
    charles_start = max(arrival_time + travel_to_charles, charles_available_start)
    charles_end = charles_start + min_meet_charles
    if charles_end <= charles_available_end:
        # Then go to Richard
        travel_to_richard = timedelta(minutes=travel_times[("Presidio", "Union Square")])
        richard_start = max(charles_end + travel_to_richard, richard_available_start)
        richard_end = richard_start + min_meet_richard
        if richard_end <= richard_available_end:
            possible_schedules.append([
                {"action": "meet", "location": "Presidio", "person": "Charles", 
                 "start_time": format_time(charles_start), "end_time": format_time(charles_end)},
                {"action": "meet", "location": "Union Square", "person": "Richard", 
                 "start_time": format_time(richard_start), "end_time": format_time(richard_end)}
            ])
    
    # Select the best schedule (earliest completion time)
    if possible_schedules:
        best_schedule = min(possible_schedules, key=lambda s: parse_time(s[-1]["end_time"]))
        return {"itinerary": best_schedule}
    else:
        return {"itinerary": []}

result = calculate_schedule()
print(json.dumps(result, indent=2))