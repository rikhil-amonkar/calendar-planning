import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def calculate_schedule():
    # Travel times dictionary: from_location -> to_location -> minutes
    travel_times = {
        "Golden Gate Park": {
            "Fisherman's Wharf": 24,
            "Bayview": 23,
            "Mission District": 17,
            "Embarcadero": 25,
            "Financial District": 26
        },
        "Fisherman's Wharf": {
            "Golden Gate Park": 25,
            "Bayview": 26,
            "Mission District": 22,
            "Embarcadero": 8,
            "Financial District": 11
        },
        "Bayview": {
            "Golden Gate Park": 22,
            "Fisherman's Wharf": 25,
            "Mission District": 13,
            "Embarcadero": 19,
            "Financial District": 19
        },
        "Mission District": {
            "Golden Gate Park": 17,
            "Fisherman's Wharf": 22,
            "Bayview": 15,
            "Embarcadero": 19,
            "Financial District": 17
        },
        "Embarcadero": {
            "Golden Gate Park": 25,
            "Fisherman's Wharf": 6,
            "Bayview": 21,
            "Mission District": 20,
            "Financial District": 5
        },
        "Financial District": {
            "Golden Gate Park": 23,
            "Fisherman's Wharf": 10,
            "Bayview": 19,
            "Mission District": 17,
            "Embarcadero": 4
        }
    }

    # People data: name -> (location, available_start, available_end, min_duration)
    people = [
        ("Joseph", "Fisherman's Wharf", time_to_minutes("8:00"), time_to_minutes("17:30"), 90),
        ("Jeffrey", "Bayview", time_to_minutes("17:30"), time_to_minutes("21:30"), 60),
        ("Kevin", "Mission District", time_to_minutes("11:15"), time_to_minutes("15:15"), 30),
        ("David", "Embarcadero", time_to_minutes("8:15"), time_to_minutes("9:00"), 30),
        ("Barbara", "Financial District", time_to_minutes("10:30"), time_to_minutes("16:30"), 15)
    ]

    # Generate all possible orders to meet people (except David who must be first)
    other_people = [p for p in people if p[0] != "David"]
    best_schedule = None
    best_meetings = 0

    # Start at 8:00 AM to have time to meet David
    start_time = time_to_minutes("8:00")
    start_location = "Golden Gate Park"

    # Try all permutations of the other people
    for perm in permutations(other_people):
        current_time = start_time
        current_location = start_location
        schedule = []
        meetings = 0

        # First meet David (must be first)
        david = [p for p in people if p[0] == "David"][0]
        travel_time = travel_times[current_location][david[1]]
        arrival_time = current_time + travel_time
        if arrival_time > david[3] - david[4]:
            continue  # Can't meet David
        start_meeting = max(arrival_time, david[2])
        end_meeting = start_meeting + david[4]
        if end_meeting > david[3]:
            continue  # Can't meet David long enough
        
        schedule.append({
            "action": "meet",
            "location": david[1],
            "person": david[0],
            "start_time": minutes_to_time(start_meeting),
            "end_time": minutes_to_time(end_meeting)
        })
        meetings += 1
        current_time = end_meeting
        current_location = david[1]

        # Now try the permutation
        valid = True
        for person in perm:
            travel_time = travel_times[current_location][person[1]]
            arrival_time = current_time + travel_time
            if arrival_time > person[3] - person[4]:
                valid = False
                break
            start_meeting = max(arrival_time, person[2])
            end_meeting = start_meeting + person[4]
            if end_meeting > person[3]:
                valid = False
                break
            schedule.append({
                "action": "meet",
                "location": person[1],
                "person": person[0],
                "start_time": minutes_to_time(start_meeting),
                "end_time": minutes_to_time(end_meeting)
            })
            meetings += 1
            current_time = end_meeting
            current_location = person[1]

        if valid and meetings > best_meetings:
            best_meetings = meetings
            best_schedule = schedule

    # After trying all permutations, pick the best one
    if best_schedule:
        return {"itinerary": best_schedule}
    else:
        # Try to find any valid schedule even if it doesn't meet everyone
        # This is a fallback in case the above doesn't find anything
        for person_order in permutations(people):
            current_time = start_time
            current_location = start_location
            schedule = []
            meetings = 0
            valid = True
            
            for person in person_order:
                if person[0] == "David" and meetings > 0:
                    continue  # David must be first
                
                travel_time = travel_times[current_location][person[1]]
                arrival_time = current_time + travel_time
                if arrival_time > person[3] - person[4]:
                    valid = False
                    break
                start_meeting = max(arrival_time, person[2])
                end_meeting = start_meeting + person[4]
                if end_meeting > person[3]:
                    valid = False
                    break
                
                schedule.append({
                    "action": "meet",
                    "location": person[1],
                    "person": person[0],
                    "start_time": minutes_to_time(start_meeting),
                    "end_time": minutes_to_time(end_meeting)
                })
                meetings += 1
                current_time = end_meeting
                current_location = person[1]
            
            if valid and meetings > best_meetings:
                best_meetings = meetings
                best_schedule = schedule
        
        if best_schedule:
            return {"itinerary": best_schedule}
        else:
            return {"itinerary": []}

result = calculate_schedule()
print(json.dumps(result, indent=2))