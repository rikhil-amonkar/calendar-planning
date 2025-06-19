import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_times = {
    "Bayview": {
        "Embarcadero": 19,
        "Richmond District": 25,
        "Fisherman's Wharf": 25
    },
    "Embarcadero": {
        "Bayview": 21,
        "Richmond District": 21,
        "Fisherman's Wharf": 6
    },
    "Richmond District": {
        "Bayview": 26,
        "Embarcadero": 19,
        "Fisherman's Wharf": 18
    },
    "Fisherman's Wharf": {
        "Bayview": 26,
        "Embarcadero": 8,
        "Richmond District": 18
    }
}

# Constraints
start_time = datetime.strptime("09:00", "%H:%M")
jessica_start = datetime.strptime("16:45", "%H:%M")
jessica_end = datetime.strptime("19:00", "%H:%M")
sandra_start = datetime.strptime("18:30", "%H:%M")
sandra_end = datetime.strptime("20:45", "%H:%M")
jason_start = datetime.strptime("16:00", "%H:%M")
jason_end = datetime.strptime("16:45", "%H:%M")

def calculate_travel_time(start, end, location):
    travel_time = travel_times["Bayview"][location]
    return (datetime.strptime(end, "%H:%M") - datetime.strptime(start, "%H:%M")).total_seconds() / 60 + travel_time

def schedule_meetings():
    meetings = []
    current_time = start_time

    # Meet Jason
    updated_jason_start = max(jason_start, current_time)
    meetings.append({
        "action": "meet",
        "location": "Fisherman's Wharf",
        "person": "Jason",
        "start_time": updated_jason_start.strftime("%H:%M"),
        "end_time": (updated_jason_start + timedelta(minutes=30)).strftime("%H:%M")
    })
    current_time = (updated_jason_start + timedelta(minutes=30))

    # Travel to Embarcadero
    travel_time_to_embarcadero = calculate_travel_time(current_time.strftime("%H:%M"), (current_time + timedelta(minutes=30)).strftime("%H:%M"), "Fisherman's Wharf")
    current_time = (current_time + timedelta(minutes=travel_time_to_embarcadero))
    current_time = datetime.strptime(current_time.strftime("%H:%M"), "%H:%M")

    # Meet Jessica
    if jessica_start < current_time:
        current_time = max(jessica_start, current_time)
    meetings.append({
        "action": "meet",
        "location": "Embarcadero",
        "person": "Jessica",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": (current_time + timedelta(minutes=30)).strftime("%H:%M")
    })
    current_time = (current_time + timedelta(minutes=30))

    # Travel to Richmond District
    travel_time_to_richmond_district = calculate_travel_time(current_time.strftime("%H:%M"), (current_time + timedelta(minutes=30)).strftime("%H:%M"), "Embarcadero")
    current_time = (current_time + timedelta(minutes=travel_time_to_richmond_district))
    current_time = datetime.strptime(current_time.strftime("%H:%M"), "%H:%M")

    # Meet Sandra
    if jessica_end < sandra_start:
        sandra_start = max(jessica_end, sandra_start)
    if sandra_start < current_time:
        current_time = max(sandra_start, current_time)
    meetings.append({
        "action": "meet",
        "location": "Richmond District",
        "person": "Sandra",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": (current_time + timedelta(minutes=120)).strftime("%H:%M")
    })
    current_time = (current_time + timedelta(minutes=120))

    return meetings

def main():
    meetings = schedule_meetings()
    print(json.dumps({"itinerary": meetings}, indent=4))

if __name__ == "__main__":
    main()