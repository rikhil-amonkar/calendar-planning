from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define friends and their details
    friends = [
        {"name": "David", "location": "Mission District", "available_start": "8:00", "available_end": "19:45", "min_duration": 45},
        {"name": "Kenneth", "location": "Alamo Square", "available_start": "14:00", "available_end": "19:45", "min_duration": 120},
        {"name": "John", "location": "Pacific Heights", "available_start": "17:00", "available_end": "20:00", "min_duration": 15},
        {"name": "Charles", "location": "Union Square", "available_start": "21:45", "available_end": "22:45", "min_duration": 60},
        {"name": "Deborah", "location": "Golden Gate Park", "available_start": "7:00", "available_end": "18:15", "min_duration": 90},
        {"name": "Karen", "location": "Sunset District", "available_start": "17:45", "available_end": "21:15", "min_duration": 15},
        {"name": "Carol", "location": "Presidio", "available_start": "8:15", "available_end": "9:15", "min_duration": 30}
    ]

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Current location starts at Chinatown, arrival time 9:00 AM
    current_location = "Chinatown"
    current_time = time_to_minutes("9:00")

    # Travel times dictionary: from -> to -> minutes
    travel_times = {
        "Chinatown": {
            "Mission District": 18,
            "Alamo Square": 17,
            "Pacific Heights": 10,
            "Union Square": 7,
            "Golden Gate Park": 23,
            "Sunset District": 29,
            "Presidio": 19
        },
        "Mission District": {
            "Chinatown": 16,
            "Alamo Square": 11,
            "Pacific Heights": 16,
            "Union Square": 15,
            "Golden Gate Park": 17,
            "Sunset District": 24,
            "Presidio": 25
        },
        "Alamo Square": {
            "Chinatown": 16,
            "Mission District": 10,
            "Pacific Heights": 10,
            "Union Square": 14,
            "Golden Gate Park": 9,
            "Sunset District": 16,
            "Presidio": 18
        },
        "Pacific Heights": {
            "Chinatown": 11,
            "Mission District": 15,
            "Alamo Square": 10,
            "Union Square": 12,
            "Golden Gate Park": 15,
            "Sunset District": 21,
            "Presidio": 11
        },
        "Union Square": {
            "Chinatown": 7,
            "Mission District": 14,
            "Alamo Square": 15,
            "Pacific Heights": 15,
            "Golden Gate Park": 22,
            "Sunset District": 26,
            "Presidio": 24
        },
        "Golden Gate Park": {
            "Chinatown": 23,
            "Mission District": 17,
            "Alamo Square": 10,
            "Pacific Heights": 16,
            "Union Square": 22,
            "Sunset District": 10,
            "Presidio": 11
        },
        "Sunset District": {
            "Chinatown": 30,
            "Mission District": 24,
            "Alamo Square": 17,
            "Pacific Heights": 21,
            "Union Square": 30,
            "Golden Gate Park": 11,
            "Presidio": 16
        },
        "Presidio": {
            "Chinatown": 21,
            "Mission District": 26,
            "Alamo Square": 18,
            "Pacific Heights": 11,
            "Union Square": 22,
            "Golden Gate Park": 12,
            "Sunset District": 15
        }
    }

    # Create variables for each friend's meeting start and end times
    meeting_vars = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        meeting_vars.append((friend, start, end))

    # Constraints for each meeting
    constraints = []
    itinerary = []
    possible_meetings = []

    # We'll try to schedule meetings in a feasible order, prioritizing those with tighter windows
    # Let's attempt to meet Carol first (only available until 9:15 AM)
    carol = next(f for f in friends if f["name"] == "Carol")
    carol_start = time_to_minutes(carol["available_start"])
    carol_end = time_to_minutes(carol["available_end"])
    travel_to_presidio = travel_times[current_location][carol["location"]]
    # Earliest possible start is current_time + travel time
    feasible_carol_start = current_time + travel_to_presidio
    if feasible_carol_start <= carol_end - carol["min_duration"]:
        # Schedule Carol
        carol_meeting_end = feasible_carol_start + carol["min_duration"]
        if carol_meeting_end <= carol_end:
            itinerary.append({
                "action": "meet",
                "person": carol["name"],
                "start_time": minutes_to_time(feasible_carol_start),
                "end_time": minutes_to_time(carol_meeting_end)
            })
            current_location = carol["location"]
            current_time = carol_meeting_end
        else:
            pass  # Cannot meet Carol

    # Next, try to meet David (available all day)
    david = next(f for f in friends if f["name"] == "David")
    travel_to_mission = travel_times[current_location][david["location"]]
    feasible_david_start = current_time + travel_to_mission
    david_start = time_to_minutes(david["available_start"])
    david_end = time_to_minutes(david["available_end"])
    if feasible_david_start <= david_end - david["min_duration"]:
        david_meeting_end = feasible_david_start + david["min_duration"]
        if david_meeting_end <= david_end:
            itinerary.append({
                "action": "meet",
                "person": david["name"],
                "start_time": minutes_to_time(feasible_david_start),
                "end_time": minutes_to_time(david_meeting_end)
            })
            current_location = david["location"]
            current_time = david_meeting_end

    # Next, try to meet Deborah (available until 6:15 PM)
    deborah = next(f for f in friends if f["name"] == "Deborah")
    travel_to_golden_gate = travel_times[current_location][deborah["location"]]
    feasible_deborah_start = current_time + travel_to_golden_gate
    deborah_start = time_to_minutes(deborah["available_start"])
    deborah_end = time_to_minutes(deborah["available_end"])
    if feasible_deborah_start <= deborah_end - deborah["min_duration"]:
        deborah_meeting_end = feasible_deborah_start + deborah["min_duration"]
        if deborah_meeting_end <= deborah_end:
            itinerary.append({
                "action": "meet",
                "person": deborah["name"],
                "start_time": minutes_to_time(feasible_deborah_start),
                "end_time": minutes_to_time(deborah_meeting_end)
            })
            current_location = deborah["location"]
            current_time = deborah_meeting_end

    # Next, try to meet Kenneth (available from 2:00 PM)
    kenneth = next(f for f in friends if f["name"] == "Kenneth")
    travel_to_alamo = travel_times[current_location][kenneth["location"]]
    feasible_kenneth_start = max(current_time + travel_to_alamo, time_to_minutes(kenneth["available_start"]))
    kenneth_end = time_to_minutes(kenneth["available_end"])
    if feasible_kenneth_start <= kenneth_end - kenneth["min_duration"]:
        kenneth_meeting_end = feasible_kenneth_start + kenneth["min_duration"]
        if kenneth_meeting_end <= kenneth_end:
            itinerary.append({
                "action": "meet",
                "person": kenneth["name"],
                "start_time": minutes_to_time(feasible_kenneth_start),
                "end_time": minutes_to_time(kenneth_meeting_end)
            })
            current_location = kenneth["location"]
            current_time = kenneth_meeting_end

    # Next, try to meet John (available from 5:00 PM)
    john = next(f for f in friends if f["name"] == "John")
    travel_to_pacific = travel_times[current_location][john["location"]]
    feasible_john_start = max(current_time + travel_to_pacific, time_to_minutes(john["available_start"]))
    john_end = time_to_minutes(john["available_end"])
    if feasible_john_start <= john_end - john["min_duration"]:
        john_meeting_end = feasible_john_start + john["min_duration"]
        if john_meeting_end <= john_end:
            itinerary.append({
                "action": "meet",
                "person": john["name"],
                "start_time": minutes_to_time(feasible_john_start),
                "end_time": minutes_to_time(john_meeting_end)
            })
            current_location = john["location"]
            current_time = john_meeting_end

    # Next, try to meet Karen (available from 5:45 PM)
    karen = next(f for f in friends if f["name"] == "Karen")
    travel_to_sunset = travel_times[current_location][karen["location"]]
    feasible_karen_start = max(current_time + travel_to_sunset, time_to_minutes(karen["available_start"]))
    karen_end = time_to_minutes(karen["available_end"])
    if feasible_karen_start <= karen_end - karen["min_duration"]:
        karen_meeting_end = feasible_karen_start + karen["min_duration"]
        if karen_meeting_end <= karen_end:
            itinerary.append({
                "action": "meet",
                "person": karen["name"],
                "start_time": minutes_to_time(feasible_karen_start),
                "end_time": minutes_to_time(karen_meeting_end)
            })
            current_location = karen["location"]
            current_time = karen_meeting_end

    # Finally, try to meet Charles (available from 9:45 PM)
    # But our current_time must be <= 21:45 - travel time to Union Square
    charles = next(f for f in friends if f["name"] == "Charles")
    travel_to_union = travel_times[current_location][charles["location"]]
    feasible_charles_start = max(current_time + travel_to_union, time_to_minutes(charles["available_start"]))
    charles_end = time_to_minutes(charles["available_end"])
    if feasible_charles_start <= charles_end - charles["min_duration"]:
        charles_meeting_end = feasible_charles_start + charles["min_duration"]
        if charles_meeting_end <= charles_end:
            itinerary.append({
                "action": "meet",
                "person": charles["name"],
                "start_time": minutes_to_time(feasible_charles_start),
                "end_time": minutes_to_time(charles_meeting_end)
            })

    # Prepare the output
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

solve_scheduling()