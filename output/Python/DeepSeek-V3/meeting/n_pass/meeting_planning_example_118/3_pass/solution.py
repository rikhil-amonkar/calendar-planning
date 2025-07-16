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
richard_location = "Union Square"
richard_min_duration = 120

charles_available_start = time_to_minutes("9:45")
charles_available_end = time_to_minutes("13:00")
charles_location = "Presidio"
charles_min_duration = 120

# Possible schedules
schedules = []

# Option 1: Meet Richard only
travel_to_richard = travel_times[(current_location, richard_location)]
richard_start = max(current_time + travel_to_richard, richard_available_start)
richard_end = richard_start + richard_min_duration

if richard_end <= richard_available_end:
    schedules.append([
        {"action": "meet", "location": richard_location, "person": "Richard", 
         "start_time": minutes_to_time(richard_start), "end_time": minutes_to_time(richard_end)}
    ])

# Option 2: Meet Charles only
travel_to_charles = travel_times[(current_location, charles_location)]
charles_start = max(current_time + travel_to_charles, charles_available_start)
charles_end = charles_start + charles_min_duration

if charles_end <= charles_available_end:
    schedules.append([
        {"action": "meet", "location": charles_location, "person": "Charles", 
         "start_time": minutes_to_time(charles_start), "end_time": minutes_to_time(charles_end)}
    ])

# Select the first valid schedule if any exist
best_schedule = schedules[0] if schedules else []

# Output the result
result = {
    "itinerary": best_schedule
}

print(json.dumps(result, indent=2))