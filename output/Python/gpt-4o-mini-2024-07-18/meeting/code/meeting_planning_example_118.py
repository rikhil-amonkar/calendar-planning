import json
from datetime import datetime, timedelta

# Constants for travel times (in minutes)
TRAVEL_TIMES = {
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Presidio"): 31,
    ("Union Square", "Presidio"): 24,
}

# Constraints
arrival_time = datetime.strptime("09:00", "%H:%M")
richard_availability_start = datetime.strptime("08:45", "%H:%M")
richard_availability_end = datetime.strptime("13:00", "%H:%M")
charles_availability_start = datetime.strptime("09:45", "%H:%M")
charles_availability_end = datetime.strptime("13:00", "%H:%M")
meeting_duration = timedelta(minutes=120)

# Functions to compute schedules
def get_travel_time(from_loc, to_loc):
    return TRAVEL_TIMES.get((from_loc, to_loc), 0)

def compute_schedule():
    schedule = []
    current_time = arrival_time
    
    # First, meet Richard
    if current_time < richard_availability_start:
        current_time = richard_availability_start
        
    end_time_richard = current_time + meeting_duration
    if end_time_richard > richard_availability_end:
        end_time_richard = richard_availability_end

    travel_to_union_square = get_travel_time("Bayview", "Union Square")
    current_time += timedelta(minutes=travel_to_union_square)

    if current_time + meeting_duration <= richard_availability_end:
        schedule.append({
            "action": "meet",
            "location": "Union Square",
            "person": "Richard",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": (current_time + meeting_duration).strftime("%H:%M"),
        })
        current_time += meeting_duration  # Update current time after meeting
    
    # Now, travel to meet Charles
    travel_to_presidio = get_travel_time("Union Square", "Presidio")
    current_time += timedelta(minutes=travel_to_presidio)
    
    if current_time < charles_availability_start:
        current_time = charles_availability_start
        
    end_time_charles = current_time + meeting_duration
    if end_time_charles > charles_availability_end:
        end_time_charles = charles_availability_end

    if current_time + meeting_duration <= charles_availability_end:
        schedule.append({
            "action": "meet",
            "location": "Presidio",
            "person": "Charles",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": (current_time + meeting_duration).strftime("%H:%M"),
        })
    
    return {"itinerary": schedule}

# Computing the schedule
itinerary = compute_schedule()

# Output the result as JSON
print(json.dumps(itinerary, indent=2))