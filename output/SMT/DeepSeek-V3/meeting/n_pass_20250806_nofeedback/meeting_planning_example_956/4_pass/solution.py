from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define friends and their constraints
    friends = {
        "William": {"location": "Alamo Square", "available_start": "15:15", "available_end": "17:15", "min_duration": 60},
        "Joshua": {"location": "Richmond District", "available_start": "07:00", "available_end": "20:00", "min_duration": 15},
        "Joseph": {"location": "Financial District", "available_start": "11:15", "available_end": "13:30", "min_duration": 15},
        "David": {"location": "Union Square", "available_start": "16:45", "available_end": "19:15", "min_duration": 45},
        "Brian": {"location": "Fisherman's Wharf", "available_start": "13:45", "available_end": "20:45", "min_duration": 105},
        "Karen": {"location": "Marina District", "available_start": "11:30", "available_end": "18:30", "min_duration": 15},
        "Anthony": {"location": "Haight-Ashbury", "available_start": "07:15", "available_end": "10:30", "min_duration": 30},
        "Matthew": {"location": "Mission District", "available_start": "17:15", "available_end": "19:15", "min_duration": 120},
        "Helen": {"location": "Pacific Heights", "available_start": "08:00", "available_end": "12:00", "min_duration": 75},
        "Jeffrey": {"location": "Golden Gate Park", "available_start": "19:00", "available_end": "21:30", "min_duration": 60}
    }

    # Define travel times between locations
    travel_times = {
        "The Castro": {
            "Alamo Square": 8, "Richmond District": 16, "Financial District": 21,
            "Union Square": 19, "Fisherman's Wharf": 24, "Marina District": 21,
            "Haight-Ashbury": 6, "Mission District": 7, "Pacific Heights": 16,
            "Golden Gate Park": 11
        },
        # ... (rest of travel times remain the same as before)
    }

    # Helper functions for time conversion
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        return f"{minutes//60:02d}:{minutes%60:02d}"

    # Create meeting variables
    meetings = {}
    for name in friends:
        meetings[name] = {
            "start": Int(f"start_{name}"),
            "end": Int(f"end_{name}"),
            "met": Bool(f"met_{name}")
        }

    # Basic constraints for each meeting
    for name in friends:
        friend = friends[name]
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]

        opt.add(meetings[name]["start"] >= available_start)
        opt.add(meetings[name]["end"] <= available_end)
        opt.add(Implies(meetings[name]["met"], meetings[name]["end"] - meetings[name]["start"] >= min_duration))
        opt.add(Implies(Not(meetings[name]["met"]), meetings[name]["start"] == meetings[name]["end"]))

    # Create a list of all possible meetings
    all_meetings = [name for name in friends]

    # Add ordering and travel time constraints
    for i in range(len(all_meetings)-1):
        m1 = all_meetings[i]
        m2 = all_meetings[i+1]
        loc1 = friends[m1]["location"]
        loc2 = friends[m2]["location"]
        travel_time = travel_times[loc1][loc2]
        
        opt.add(Implies(And(meetings[m1]["met"], meetings[m2]["met"]),
                     meetings[m2]["start"] >= meetings[m1]["end"] + travel_time))

    # Maximize the number of friends met
    opt.maximize(Sum([If(meetings[name]["met"], 1, 0) for name in friends))

    # Solve and get results
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for name in friends:
            if is_true(model[meetings[name]["met"]]):
                start = model[meetings[name]["start"]].as_long()
                end = model[meetings[name]["end"]].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
        # Sort by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))