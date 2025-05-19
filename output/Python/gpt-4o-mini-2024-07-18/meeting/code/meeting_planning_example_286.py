import json
from datetime import datetime, timedelta

# Define travel distances
travel_times = {
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Sunset District"): 26,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Sunset District"): 24,
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Sunset District"): 23,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Bayview"): 22,
}

# Define meeting constraints
constraints = {
    "Rebecca": {
        "location": "Mission District",
        "start": datetime.strptime("11:30", "%H:%M"),
        "end": datetime.strptime("20:15", "%H:%M"),
        "duration": timedelta(minutes=120),
    },
    "Karen": {
        "location": "Bayview",
        "start": datetime.strptime("12:45", "%H:%M"),
        "end": datetime.strptime("15:00", "%H:%M"),
        "duration": timedelta(minutes=120),
    },
    "Carol": {
        "location": "Sunset District",
        "start": datetime.strptime("10:15", "%H:%M"),
        "end": datetime.strptime("11:45", "%H:%M"),
        "duration": timedelta(minutes=30),
    },
}

# Initialize travel time from starting point
current_time = datetime.strptime("09:00", "%H:%M")
itinerary = []

# Meeting with Carol
def meet_with_carol():
    global current_time
    travel_to_carol = travel_times[("Union Square", "Sunset District")]
    arrive_time = current_time + timedelta(minutes=travel_to_carol)
    if arrive_time >= constraints["Carol"]["start"] and arrive_time <= constraints["Carol"]["end"]:
        meeting_start = max(arrive_time, constraints["Carol"]["start"])
        meeting_end = meeting_start + constraints["Carol"]["duration"]
        if meeting_end <= constraints["Carol"]["end"]:
            itinerary.append({
                "action": "meet",
                "location": "Sunset District",
                "person": "Carol",
                "start_time": meeting_start.strftime("%H:%M"),
                "end_time": meeting_end.strftime("%H:%M"),
            })
            current_time = meeting_end + timedelta(minutes=travel_times[("Sunset District", "Mission District")])

meet_with_carol()

# Meeting with Rebecca
def meet_with_rebecca():
    global current_time
    travel_to_rebecca = travel_times[("Mission District", "Union Square")]
    travel_to_union = travel_times[("Union Square", "Mission District")]
    arrive_time = current_time + timedelta(minutes=travel_to_union)
    if arrive_time < constraints["Rebecca"]["start"]:
        arrive_time = constraints["Rebecca"]["start"]
    
    meeting_start = arrive_time
    meeting_end = meeting_start + constraints["Rebecca"]["duration"]
    if meeting_end <= constraints["Rebecca"]["end"]:
        itinerary.append({
            "action": "meet",
            "location": "Mission District",
            "person": "Rebecca",
            "start_time": meeting_start.strftime("%H:%M"),
            "end_time": meeting_end.strftime("%H:%M"),
        })
        current_time = meeting_end + travel_times[("Mission District", "Bayview")]

meet_with_rebecca()

# Meeting with Karen
def meet_with_karen():
    global current_time
    travel_to_karen = travel_times[("Bayview", "Mission District")]
    arrive_time = current_time + timedelta(minutes=travel_to_karen)
    if arrive_time < constraints["Karen"]["start"]:
        arrive_time = constraints["Karen"]["start"]

    meeting_start = arrive_time
    meeting_end = meeting_start + constraints["Karen"]["duration"]
    if meeting_end <= constraints["Karen"]["end"]:
        itinerary.append({
            "action": "meet",
            "location": "Bayview",
            "person": "Karen",
            "start_time": meeting_start.strftime("%H:%M"),
            "end_time": meeting_end.strftime("%H:%M"),
        })

meet_with_karen()

# Return the output as a JSON format
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))