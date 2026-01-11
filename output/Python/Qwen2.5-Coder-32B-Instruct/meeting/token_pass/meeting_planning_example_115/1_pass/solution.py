import json
from datetime import datetime, timedelta

# Define travel times in minutes
travel_times = {
    ("richmond_district", "pacific_heights"): 10,
    ("richmond_district", "marina_district"): 9,
    ("pacific_heights", "richmond_district"): 12,
    ("pacific_heights", "marina_district"): 6,
    ("marina_district", "richmond_district"): 11,
    ("marina_district", "pacific_heights"): 7
}

# Define meeting constraints
constraints = {
    "carol": {
        "location": "marina_district",
        "available_start": datetime.strptime("11:30", "%H:%M"),
        "available_end": datetime.strptime("15:00", "%H:%M"),
        "min_duration": 60
    },
    "jessica": {
        "location": "pacific_heights",
        "available_start": datetime.strptime("15:30", "%H:%M"),
        "available_end": datetime.strptime("16:45", "%H:%M"),
        "min_duration": 45
    }
}

def find_meeting_schedule(start_location, start_time):
    itinerary = []
    
    # Convert start time to datetime object
    current_time = datetime.strptime(start_time, "%H:%M")
    
    # Try to meet Carol first
    carol_constraint = constraints["carol"]
    carol_start = max(current_time + timedelta(minutes=travel_times[(start_location, carol_constraint["location"])]), carol_constraint["available_start"])
    carol_end = carol_start + timedelta(minutes=carol_constraint["min_duration"])
    
    if carol_end <= carol_constraint["available_end"]:
        # Add Carol meeting to itinerary
        itinerary.append({
            "action": "meet",
            "location": carol_constraint["location"],
            "person": "Carol",
            "start_time": carol_start.strftime("%H:%M"),
            "end_time": carol_end.strftime("%H:%M")
        })
        current_time = carol_end
    else:
        return []  # No valid schedule
    
    # Try to meet Jessica next
    jessica_constraint = constraints["jessica"]
    jessica_travel_time = travel_times[(itinerary[-1]["location"], jessica_constraint["location"])]
    jessica_start = max(current_time + timedelta(minutes=jessica_travel_time), jessica_constraint["available_start"])
    jessica_end = jessica_start + timedelta(minutes=jessica_constraint["min_duration"])
    
    if jessica_end <= jessica_constraint["available_end"]:
        # Add Jessica meeting to itinerary
        itinerary.append({
            "action": "meet",
            "location": jessica_constraint["location"],
            "person": "Jessica",
            "start_time": jessica_start.strftime("%H:%M"),
            "end_time": jessica_end.strftime("%H:%M")
        })
    else:
        return []  # No valid schedule
    
    return itinerary

# Start location and time
start_location = "richmond_district"
start_time = "9:00"

# Find the optimal meeting schedule
optimal_schedule = find_meeting_schedule(start_location, start_time)

# Output the result as a JSON-formatted dictionary
output_json = json.dumps({"itinerary": optimal_schedule}, indent=2)
print(output_json)