from z3 import *
import json

def main():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their constraints
    friends = [
        {"name": "Joshua", "location": "Embarcadero", "start_available": 9*60 + 45, "end_available": 18*60, "min_duration": 105},
        {"name": "Jeffrey", "location": "Bayview", "start_available": 9*60 + 45, "end_available": 20*60 + 15, "min_duration": 75},
        {"name": "Charles", "location": "Union Square", "start_available": 10*60 + 45, "end_available": 20*60 + 15, "min_duration": 120},
        {"name": "Joseph", "location": "Chinatown", "start_available": 7*60, "end_available": 15*60 + 30, "min_duration": 60},
        {"name": "Elizabeth", "location": "Sunset District", "start_available": 9*60, "end_available": 9*60 + 45, "min_duration": 45},
        {"name": "Matthew", "location": "Golden Gate Park", "start_available": 11*60, "end_available": 19*60 + 30, "min_duration": 45},
        {"name": "Carol", "location": "Financial District", "start_available": 10*60 + 45, "end_available": 11*60 + 15, "min_duration": 15},
        {"name": "Paul", "location": "Haight-Ashbury", "start_available": 19*60 + 15, "end_available": 20*60 + 30, "min_duration": 15},
        {"name": "Rebecca", "location": "Mission District", "start_available": 17*60, "end_available": 21*60 + 45, "min_duration": 45}
    ]

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Marina District": {
            "Embarcadero": 14,
            "Bayview": 27,
            "Union Square": 16,
            "Chinatown": 15,
            "Sunset District": 19,
            "Golden Gate Park": 18,
            "Financial District": 17,
            "Haight-Ashbury": 16,
            "Mission District": 20
        },
        "Embarcadero": {
            "Marina District": 12,
            "Bayview": 21,
            "Union Square": 10,
            "Chinatown": 7,
            "Sunset District": 30,
            "Golden Gate Park": 25,
            "Financial District": 5,
            "Haight-Ashbury": 21,
            "Mission District": 20
        },
        "Bayview": {
            "Marina District": 27,
            "Embarcadero": 19,
            "Union Square": 18,
            "Chinatown": 19,
            "Sunset District": 23,
            "Golden Gate Park": 22,
            "Financial District": 19,
            "Haight-Ashbury": 19,
            "Mission District": 13
        },
        "Union Square": {
            "Marina District": 18,
            "Embarcadero": 11,
            "Bayview": 15,
            "Chinatown": 7,
            "Sunset District": 27,
            "Golden Gate Park": 22,
            "Financial District": 9,
            "Haight-Ashbury": 18,
            "Mission District": 14
        },
        "Chinatown": {
            "Marina District": 12,
            "Embarcadero": 5,
            "Bayview": 20,
            "Union Square": 7,
            "Sunset District": 29,
            "Golden Gate Park": 23,
            "Financial District": 5,
            "Haight-Ashbury": 19,
            "Mission District": 17
        },
        "Sunset District": {
            "Marina District": 21,
            "Embarcadero": 30,
            "Bayview": 22,
            "Union Square": 30,
            "Chinatown": 30,
            "Golden Gate Park": 11,
            "Financial District": 30,
            "Haight-Ashbury": 15,
            "Mission District": 25
        },
        "Golden Gate Park": {
            "Marina District": 16,
            "Embarcadero": 25,
            "Bayview": 23,
            "Union Square": 22,
            "Chinatown": 23,
            "Sunset District": 10,
            "Financial District": 26,
            "Haight-Ashbury": 7,
            "Mission District": 17
        },
        "Financial District": {
            "Marina District": 15,
            "Embarcadero": 4,
            "Bayview": 19,
            "Union Square": 9,
            "Chinatown": 5,
            "Sunset District": 30,
            "Golden Gate Park": 23,
            "Haight-Ashbury": 19,
            "Mission District": 17
        },
        "Haight-Ashbury": {
            "Marina District": 17,
            "Embarcadero": 20,
            "Bayview": 18,
            "Union Square": 19,
            "Chinatown": 19,
            "Sunset District": 15,
            "Golden Gate Park": 7,
            "Financial District": 21,
            "Mission District": 11
        },
        "Mission District": {
            "Marina District": 19,
            "Embarcadero": 19,
            "Bayview": 14,
            "Union Square": 15,
            "Chinatown": 16,
            "Sunset District": 24,
            "Golden Gate Park": 17,
            "Financial District": 15,
            "Haight-Ashbury": 12
        }
    }

    # Create variables for each friend: start and end times, and a flag indicating if the meeting is scheduled
    meeting_vars = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        scheduled = Bool(f"scheduled_{friend['name']}")
        meeting_vars.append({
            "name": friend["name"],
            "location": friend["location"],
            "start": start,
            "end": end,
            "scheduled": scheduled,
            "min_duration": friend["min_duration"],
            "start_available": friend["start_available"],
            "end_available": friend["end_available"]
        })

    # Current location starts at Marina District
    current_location = "Marina District"
    current_time = 9 * 60  # 9:00 AM in minutes

    # Constraints for each meeting
    for meeting in meeting_vars:
        # If scheduled, meeting must fit within availability and have min duration
        s.add(Implies(meeting["scheduled"], 
                      And(meeting["start"] >= meeting["start_available"],
                          meeting["end"] <= meeting["end_available"],
                          meeting["end"] - meeting["start"] >= meeting["min_duration"])))

    # Ensure meetings don't overlap and account for travel time
    for i in range(len(meeting_vars)):
        for j in range(len(meeting_vars)):
            if i != j:
                # Either i is before j or vice versa, with travel time
                m1 = meeting_vars[i]
                m2 = meeting_vars[j]
                travel_time = travel_times[m1["location"]][m2["location"]]
                s.add(Implies(And(m1["scheduled"], m2["scheduled"]),
                              Or(m1["end"] + travel_time <= m2["start"],
                                 m2["end"] + travel_time <= m1["start"])))

    # The first meeting must start after current_time + travel time from Marina District
    for meeting in meeting_vars:
        travel_time = travel_times[current_location][meeting["location"]]
        s.add(Implies(meeting["scheduled"], meeting["start"] >= current_time + travel_time))

    # Maximize the number of scheduled meetings
    total_scheduled = Sum([If(m["scheduled"], 1, 0) for m in meeting_vars])
    s.maximize(total_scheduled)

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for meeting in meeting_vars:
            if is_true(model.eval(meeting["scheduled"])):
                start_val = model.eval(meeting["start"]).as_long()
                end_val = model.eval(meeting["end"]).as_long()
                start_hh = start_val // 60
                start_mm = start_val % 60
                end_hh = end_val // 60
                end_mm = end_val % 60
                itinerary.append({
                    "action": "meet",
                    "person": meeting["name"],
                    "start_time": f"{start_hh:02d}:{start_mm:02d}",
                    "end_time": f"{end_hh:02d}:{end_mm:02d}"
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: (int(x["start_time"][:2]), int(x["start_time"][3:5]))
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()