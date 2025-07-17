from z3 import *
import json

def solve_scheduling():
    s = Solver()

    # Define friends and their constraints
    friends = {
        "David": {"location": "Mission District", "start": 8*60, "end": 19*60+45, "duration": 45},
        "Kenneth": {"location": "Alamo Square", "start": 14*60, "end": 19*60+45, "duration": 120},
        "John": {"location": "Pacific Heights", "start": 17*60, "end": 20*60, "duration": 15},
        "Charles": {"location": "Union Square", "start": 21*60+45, "end": 22*60+45, "duration": 60},
        "Deborah": {"location": "Golden Gate Park", "start": 7*60, "end": 18*60+15, "duration": 90},
        "Karen": {"location": "Sunset District", "start": 17*60+45, "end": 21*60+15, "duration": 15},
        "Carol": {"location": "Presidio", "start": 8*60+15, "end": 9*60+15, "duration": 30}
    }

    # Travel times between locations
    travel_times = {
        "Chinatown": {"Mission District": 18, "Alamo Square": 17, "Pacific Heights": 10, 
                      "Union Square": 7, "Golden Gate Park": 23, "Sunset District": 29, "Presidio": 19},
        "Mission District": {"Chinatown": 16, "Alamo Square": 11, "Pacific Heights": 16,
                           "Union Square": 15, "Golden Gate Park": 17, "Sunset District": 24, "Presidio": 25},
        "Alamo Square": {"Chinatown": 16, "Mission District": 10, "Pacific Heights": 10,
                        "Union Square": 14, "Golden Gate Park": 9, "Sunset District": 16, "Presidio": 18},
        "Pacific Heights": {"Chinatown": 11, "Mission District": 15, "Alamo Square": 10,
                          "Union Square": 12, "Golden Gate Park": 15, "Sunset District": 21, "Presidio": 11},
        "Union Square": {"Chinatown": 7, "Mission District": 14, "Alamo Square": 15,
                       "Pacific Heights": 15, "Golden Gate Park": 22, "Sunset District": 26, "Presidio": 24},
        "Golden Gate Park": {"Chinatown": 23, "Mission District": 17, "Alamo Square": 10,
                            "Pacific Heights": 16, "Union Square": 22, "Sunset District": 10, "Presidio": 11},
        "Sunset District": {"Chinatown": 30, "Mission District": 24, "Alamo Square": 17,
                           "Pacific Heights": 21, "Union Square": 30, "Golden Gate Park": 11, "Presidio": 16},
        "Presidio": {"Chinatown": 21, "Mission District": 26, "Alamo Square": 18,
                    "Pacific Heights": 11, "Union Square": 22, "Golden Gate Park": 12, "Sunset District": 15}
    }

    # Create variables for each meeting
    meeting_vars = {}
    for name in friends:
        meeting_vars[name] = {
            "start": Int(f"start_{name}"),
            "end": Int(f"end_{name}"),
            "scheduled": Bool(f"scheduled_{name}")
        }

    # Current time starts at 9:00 AM (540 minutes)
    current_time = 540
    current_location = "Chinatown"
    itinerary = []

    # First try to meet Carol (only available 8:15-9:15)
    carol = friends["Carol"]
    travel_time = travel_times[current_location][carol["location"]]
    earliest_start = current_time + travel_time
    if earliest_start <= carol["end"] - carol["duration"]:
        meeting_start = earliest_start
        meeting_end = meeting_start + carol["duration"]
        itinerary.append({
            "action": "meet",
            "person": "Carol",
            "start_time": f"{meeting_start//60:02d}:{meeting_start%60:02d}",
            "end_time": f"{meeting_end//60:02d}:{meeting_end%60:02d}"
        })
        current_time = meeting_end
        current_location = carol["location"]

    # Now try to schedule other meetings in optimal order
    # Deborah (Golden Gate Park) - available all day
    deborah = friends["Deborah"]
    travel_time = travel_times[current_location][deborah["location"]]
    earliest_start = current_time + travel_time
    if earliest_start <= deborah["end"] - deborah["duration"]:
        meeting_start = earliest_start
        meeting_end = meeting_start + deborah["duration"]
        itinerary.append({
            "action": "meet",
            "person": "Deborah",
            "start_time": f"{meeting_start//60:02d}:{meeting_start%60:02d}",
            "end_time": f"{meeting_end//60:02d}:{meeting_end%60:02d}"
        })
        current_time = meeting_end
        current_location = deborah["location"]

    # David (Mission District) - available until 7:45pm
    david = friends["David"]
    travel_time = travel_times[current_location][david["location"]]
    earliest_start = current_time + travel_time
    if earliest_start <= david["end"] - david["duration"]:
        meeting_start = earliest_start
        meeting_end = meeting_start + david["duration"]
        itinerary.append({
            "action": "meet",
            "person": "David",
            "start_time": f"{meeting_start//60:02d}:{meeting_start%60:02d}",
            "end_time": f"{meeting_end//60:02d}:{meeting_end%60:02d}"
        })
        current_time = meeting_end
        current_location = david["location"]

    # Kenneth (Alamo Square) - available 2:00pm-7:45pm
    kenneth = friends["Kenneth"]
    travel_time = travel_times[current_location][kenneth["location"]]
    earliest_start = max(current_time + travel_time, kenneth["start"])
    if earliest_start <= kenneth["end"] - kenneth["duration"]:
        meeting_start = earliest_start
        meeting_end = meeting_start + kenneth["duration"]
        itinerary.append({
            "action": "meet",
            "person": "Kenneth",
            "start_time": f"{meeting_start//60:02d}:{meeting_start%60:02d}",
            "end_time": f"{meeting_end//60:02d}:{meeting_end%60:02d}"
        })
        current_time = meeting_end
        current_location = kenneth["location"]

    # John (Pacific Heights) - available 5:00pm-8:00pm
    john = friends["John"]
    travel_time = travel_times[current_location][john["location"]]
    earliest_start = max(current_time + travel_time, john["start"])
    if earliest_start <= john["end"] - john["duration"]:
        meeting_start = earliest_start
        meeting_end = meeting_start + john["duration"]
        itinerary.append({
            "action": "meet",
            "person": "John",
            "start_time": f"{meeting_start//60:02d}:{meeting_start%60:02d}",
            "end_time": f"{meeting_end//60:02d}:{meeting_end%60:02d}"
        })
        current_time = meeting_end
        current_location = john["location"]

    # Karen (Sunset District) - available 5:45pm-9:15pm
    karen = friends["Karen"]
    travel_time = travel_times[current_location][karen["location"]]
    earliest_start = max(current_time + travel_time, karen["start"])
    if earliest_start <= karen["end"] - karen["duration"]:
        meeting_start = earliest_start
        meeting_end = meeting_start + karen["duration"]
        itinerary.append({
            "action": "meet",
            "person": "Karen",
            "start_time": f"{meeting_start//60:02d}:{meeting_start%60:02d}",
            "end_time": f"{meeting_end//60:02d}:{meeting_end%60:02d}"
        })
        current_time = meeting_end
        current_location = karen["location"]

    # Charles (Union Square) - available 9:45pm-10:45pm
    charles = friends["Charles"]
    travel_time = travel_times[current_location][charles["location"]]
    earliest_start = max(current_time + travel_time, charles["start"])
    if earliest_start <= charles["end"] - charles["duration"]:
        meeting_start = earliest_start
        meeting_end = meeting_start + charles["duration"]
        itinerary.append({
            "action": "meet",
            "person": "Charles",
            "start_time": f"{meeting_start//60:02d}:{meeting_start%60:02d}",
            "end_time": f"{meeting_end//60:02d}:{meeting_end%60:02d}"
        })

    return {"itinerary": itinerary}

solution = solve_scheduling()
print(json.dumps(solution, indent=2))