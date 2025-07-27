from z3 import *
import json

def solve_scheduling():
    s = Optimize()  # Using Optimize to maximize number of meetings

    # Friends data
    friends = [
        {"name": "Robert", "location": "Chinatown", "available_start": "7:45", "available_end": "17:30", "duration": 120},
        {"name": "David", "location": "Sunset District", "available_start": "12:30", "available_end": "19:45", "duration": 45},
        {"name": "Matthew", "location": "Alamo Square", "available_start": "8:45", "available_end": "13:45", "duration": 90},
        {"name": "Jessica", "location": "Financial District", "available_start": "9:30", "available_end": "18:45", "duration": 45},
        {"name": "Melissa", "location": "North Beach", "available_start": "7:15", "available_end": "16:45", "duration": 45},
        {"name": "Mark", "location": "Embarcadero", "available_start": "15:15", "available_end": "17:00", "duration": 45},
        {"name": "Deborah", "location": "Presidio", "available_start": "19:00", "available_end": "19:45", "duration": 45},
        {"name": "Karen", "location": "Golden Gate Park", "available_start": "19:30", "available_end": "22:00", "duration": 120},
        {"name": "Laura", "location": "Bayview", "available_start": "21:15", "available_end": "22:15", "duration": 15}
    ]

    # Time conversion functions
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Travel times dictionary
    travel_times = {
        ("Richmond District", "Chinatown"): 20,
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Bayview"): 27,
        ("Chinatown", "Richmond District"): 20,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Bayview"): 20,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Bayview"): 22,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Bayview"): 16,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Bayview"): 19,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Bayview"): 25,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Bayview"): 21,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Bayview"): 31,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Bayview"): 23,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Sunset District"): 23,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "North Beach"): 22,
        ("Bayview", "Embarcadero"): 19,
        ("Bayview", "Presidio"): 32,
        ("Bayview", "Golden Gate Park"): 22
    }

    # Create meeting variables
    meetings = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        attended = Bool(f"attended_{friend['name']}")
        meetings.append({
            "name": friend["name"],
            "location": friend["location"],
            "start": start,
            "end": end,
            "attended": attended,
            "duration": friend["duration"],
            "available_start": time_to_minutes(friend["available_start"]),
            "available_end": time_to_minutes(friend["available_end"])
        })

    # Starting point
    current_location = "Richmond District"
    current_time = time_to_minutes("9:00")

    # Basic constraints for each meeting
    for meeting in meetings:
        # If attended, must be within availability window
        s.add(Implies(meeting["attended"], meeting["start"] >= meeting["available_start"]))
        s.add(Implies(meeting["attended"], meeting["end"] <= meeting["available_end"]))
        s.add(Implies(meeting["attended"], meeting["end"] == meeting["start"] + meeting["duration"]))

    # Create order variables to sequence meetings
    order = {m["name"]: Int(f"order_{m['name']}") for m in meetings}
    s.add(Distinct([order[m["name"]] for m in meetings]))
    for m in meetings:
        s.add(order[m["name"]] >= 0)
        s.add(order[m["name"]] < len(meetings))

    # Sequence constraints
    for i, m1 in enumerate(meetings):
        for j, m2 in enumerate(meetings):
            if i != j:
                # If m1 comes before m2 and both are attended
                before = And(m1["attended"], m2["attended"], order[m1["name"]] < order[m2["name"]])
                # Then m2 must start after m1 ends plus travel time
                travel_time = travel_times.get((m1["location"], m2["location"]), 0)
                s.add(Implies(before, m2["start"] >= m1["end"] + travel_time))

    # First meeting must be after 9:00 AM plus travel time
    for m in meetings:
        travel_time = travel_times.get((current_location, m["location"]), 0)
        s.add(Implies(m["attended"], m["start"] >= current_time + travel_time))

    # Maximize number of meetings attended
    s.maximize(Sum([If(m["attended"], 1, 0) for m in meetings]))

    # Check solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for meeting in meetings:
            if is_true(model[meeting["attended"]]):
                start_time = model[meeting["start"]].as_long()
                end_time = model[meeting["end"]].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": meeting["name"],
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time),
                    "location": meeting["location"]
                })
        
        # Sort by order
        itinerary.sort(key=lambda x: model[order[x["person"]]].as_long())
        
        # Verify travel times
        for i in range(len(itinerary)-1):
            current = itinerary[i]
            next_meet = itinerary[i+1]
            travel_time = travel_times.get((current["location"], next_meet["location"]), 0)
            actual_gap = time_to_minutes(next_meet["start_time"]) - time_to_minutes(current["end_time"])
            assert actual_gap >= travel_time, f"Travel time violation between {current['person']} and {next_meet['person']}"
        
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the solver
result = solve_scheduling()
print(json.dumps(result, indent=2))