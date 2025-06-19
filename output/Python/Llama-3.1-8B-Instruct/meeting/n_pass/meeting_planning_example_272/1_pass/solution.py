import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    "Russian Hill": {
        "Nob Hill": 5,
        "Mission District": 16,
        "Embarcadero": 8
    },
    "Nob Hill": {
        "Russian Hill": 5,
        "Mission District": 13,
        "Embarcadero": 9
    },
    "Mission District": {
        "Russian Hill": 15,
        "Nob Hill": 12,
        "Embarcadero": 19
    },
    "Embarcadero": {
        "Russian Hill": 8,
        "Nob Hill": 10,
        "Mission District": 20
    }
}

# Constraints
start_time = datetime.strptime('09:00', '%H:%M')
patricia_start_time = datetime.strptime('18:30', '%H:%M')
patricia_end_time = datetime.strptime('21:45', '%H:%M')
patricia_meeting_time = timedelta(minutes=90)
ashley_start_time = datetime.strptime('20:30', '%H:%M')
ashley_end_time = datetime.strptime('21:15', '%H:%M')
ashley_meeting_time = timedelta(minutes=45)
timothy_start_time = datetime.strptime('09:45', '%H:%M')
timothy_end_time = datetime.strptime('17:45', '%H:%M')
timothy_meeting_time = timedelta(minutes=120)

def calculate_travel_time(location1, location2):
    return travel_distances[location1][location2]

def is_valid_meeting(start_time, end_time, meeting_time):
    return end_time - start_time >= meeting_time

def compute_meeting_schedule():
    itinerary = []
    current_time = start_time

    # Meet Timothy
    if is_valid_meeting(current_time, timothy_end_time, timothy_meeting_time):
        itinerary.append({
            "action": "meet",
            "location": "Embarcadero",
            "person": "Timothy",
            "start_time": current_time.strftime('%H:%M'),
            "end_time": (current_time + timothy_meeting_time).strftime('%H:%M')
        })
        current_time += timothy_meeting_time

    # Travel to Nob Hill
    current_time += timedelta(minutes=calculate_travel_time("Embarcadero", "Nob Hill"))

    # Wait for Patricia
    wait_time = patricia_start_time - current_time
    if wait_time.total_seconds() > 0:
        itinerary.append({
            "action": "wait",
            "location": "Nob Hill",
            "person": "Patricia",
            "start_time": current_time.strftime('%H:%M'),
            "end_time": (current_time + wait_time).strftime('%H:%M')
        })
        current_time += wait_time

    # Meet Patricia
    if is_valid_meeting(current_time, patricia_end_time, patricia_meeting_time):
        itinerary.append({
            "action": "meet",
            "location": "Nob Hill",
            "person": "Patricia",
            "start_time": current_time.strftime('%H:%M'),
            "end_time": (current_time + patricia_meeting_time).strftime('%H:%M')
        })
        current_time += patricia_meeting_time

    # Travel to Mission District
    current_time += timedelta(minutes=calculate_travel_time("Nob Hill", "Mission District"))

    # Wait for Ashley
    wait_time = ashley_start_time - current_time
    if wait_time.total_seconds() > 0:
        itinerary.append({
            "action": "wait",
            "location": "Mission District",
            "person": "Ashley",
            "start_time": current_time.strftime('%H:%M'),
            "end_time": (current_time + wait_time).strftime('%H:%M')
        })
        current_time += wait_time

    # Meet Ashley
    if is_valid_meeting(current_time, ashley_end_time, ashley_meeting_time):
        itinerary.append({
            "action": "meet",
            "location": "Mission District",
            "person": "Ashley",
            "start_time": current_time.strftime('%H:%M'),
            "end_time": (current_time + ashley_meeting_time).strftime('%H:%M')
        })
        current_time += ashley_meeting_time

    return itinerary

def main():
    schedule = compute_meeting_schedule()
    print(json.dumps({"itinerary": schedule}, indent=4))

if __name__ == "__main__":
    main()