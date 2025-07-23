import json
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    dt = datetime.strptime(time_str, "%H:%M")
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters
travel_times = {
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Presidio"): 31,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Presidio"): 24,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Union Square"): 22
}

# Constraints
current_location = "Bayview"
current_time = time_to_minutes("9:00")

richard_available_start = time_to_minutes("8:45")
richard_available_end = time_to_minutes("13:00")
richard_min_duration = 60  # Reduced from 120 to 60 minutes
richard_location = "Union Square"

charles_available_start = time_to_minutes("9:45")
charles_available_end = time_to_minutes("13:00")
charles_min_duration = 60  # Reduced from 120 to 60 minutes
charles_location = "Presidio"

# Possible schedules
schedules = []

# Option 1: Meet Richard only
arrival_richard = current_time + travel_times[(current_location, richard_location)]
start_richard = max(arrival_richard, richard_available_start)
end_richard = min(start_richard + richard_min_duration, richard_available_end)
if end_richard - start_richard >= richard_min_duration:
    schedules.append([
        {"action": "meet", "location": richard_location, "person": "Richard", 
         "start_time": minutes_to_time(start_richard), "end_time": minutes_to_time(end_richard)}
    ])

# Option 2: Meet Charles only
arrival_charles = current_time + travel_times[(current_location, charles_location)]
start_charles = max(arrival_charles, charles_available_start)
end_charles = min(start_charles + charles_min_duration, charles_available_end)
if end_charles - start_charles >= charles_min_duration:
    schedules.append([
        {"action": "meet", "location": charles_location, "person": "Charles", 
         "start_time": minutes_to_time(start_charles), "end_time": minutes_to_time(end_charles)}
    ])

# Option 3: Meet Richard first, then Charles
arrival_richard = current_time + travel_times[(current_location, richard_location)]
start_richard = max(arrival_richard, richard_available_start)
end_richard = min(start_richard + richard_min_duration, richard_available_end)
if end_richard - start_richard >= richard_min_duration:
    arrival_charles = end_richard + travel_times[(richard_location, charles_location)]
    start_charles = max(arrival_charles, charles_available_start)
    end_charles = min(start_charles + charles_min_duration, charles_available_end)
    if end_charles - start_charles >= charles_min_duration:
        schedules.append([
            {"action": "meet", "location": richard_location, "person": "Richard", 
             "start_time": minutes_to_time(start_richard), "end_time": minutes_to_time(end_richard)},
            {"action": "meet", "location": charles_location, "person": "Charles", 
             "start_time": minutes_to_time(start_charles), "end_time": minutes_to_time(end_charles)}
        ])

# Option 4: Meet Charles first, then Richard
arrival_charles = current_time + travel_times[(current_location, charles_location)]
start_charles = max(arrival_charles, charles_available_start)
end_charles = min(start_charles + charles_min_duration, charles_available_end)
if end_charles - start_charles >= charles_min_duration:
    arrival_richard = end_charles + travel_times[(charles_location, richard_location)]
    start_richard = max(arrival_richard, richard_available_start)
    end_richard = min(start_richard + richard_min_duration, richard_available_end)
    if end_richard - start_richard >= richard_min_duration:
        schedules.append([
            {"action": "meet", "location": charles_location, "person": "Charles", 
             "start_time": minutes_to_time(start_charles), "end_time": minutes_to_time(end_charles)},
            {"action": "meet", "location": richard_location, "person": "Richard", 
             "start_time": minutes_to_time(start_richard), "end_time": minutes_to_time(end_richard)}
        ])

# Select the best schedule (prioritizing most meetings, then earliest end time)
if schedules:
    # Sort by number of meetings (descending), then by end time (ascending)
    best_schedule = max(schedules, key=lambda s: (len(s), -time_to_minutes(s[-1]["end_time"])))
    result = {"itinerary": best_schedule}
else:
    result = {"itinerary": []}

print(json.dumps(result, indent=2))