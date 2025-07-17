from z3 import *
import json

def main():
    # Initialize solver
    s = Optimize()

    # Define friends and their details
    friends = [
        {"name": "Jeffrey", "location": "Fisherman's Wharf", "start_window": 10*60 + 15, "end_window": 13*60, "min_duration": 90},
        {"name": "Ronald", "location": "Alamo Square", "start_window": 7*60 + 45, "end_window": 14*60 + 45, "min_duration": 120},
        {"name": "Jason", "location": "Financial District", "start_window": 10*60 + 45, "end_window": 16*60, "min_duration": 105},
        {"name": "Melissa", "location": "Union Square", "start_window": 17*60 + 45, "end_window": 18*60 + 15, "min_duration": 15},
        {"name": "Elizabeth", "location": "Sunset District", "start_window": 14*60 + 45, "end_window": 17*60 + 30, "min_duration": 105},
        {"name": "Margaret", "location": "Embarcadero", "start_window": 13*60 + 15, "end_window": 19*60, "min_duration": 90},
        {"name": "George", "location": "Golden Gate Park", "start_window": 19*60, "end_window": 22*60, "min_duration": 75},
        {"name": "Richard", "location": "Chinatown", "start_window": 9*60 + 30, "end_window": 21*60, "min_duration": 15},
        {"name": "Laura", "location": "Richmond District", "start_window": 9*60 + 45, "end_window": 18*60, "min_duration": 60}
    ]

    # Travel times dictionary
    travel_times = {
        "Presidio": {
            "Fisherman's Wharf": 19, "Alamo Square": 19, "Financial District": 23,
            "Union Square": 22, "Sunset District": 15, "Embarcadero": 20,
            "Golden Gate Park": 12, "Chinatown": 21, "Richmond District": 7
        },
        "Fisherman's Wharf": {
            "Presidio": 17, "Alamo Square": 21, "Financial District": 11,
            "Union Square": 13, "Sunset District": 27, "Embarcadero": 8,
            "Golden Gate Park": 25, "Chinatown": 12, "Richmond District": 18
        },
        # ... (rest of travel times remain the same)
    }

    # Create variables and basic constraints
    for friend in friends:
        friend["start"] = Int(f"start_{friend['name']}")
        friend["end"] = Int(f"end_{friend['name']}")
        s.add(friend["start"] >= friend["start_window"] - 9*60)
        s.add(friend["end"] <= friend["end_window"] - 9*60)
        s.add(friend["end"] == friend["start"] + friend["min_duration"])
        s.add(friend["start"] >= 0)

    # Create meeting sequence variables
    num_friends = len(friends)
    sequence = [Int(f"seq_{i}") for i in range(num_friends)]
    s.add(Distinct(sequence))
    for i in range(num_friends):
        s.add(sequence[i] >= 0, sequence[i] < num_friends)

    # Add travel time constraints between consecutive meetings
    for i in range(num_friends - 1):
        current = sequence[i]
        next_ = sequence[i + 1]
        for j in range(num_friends):
            for k in range(num_friends):
                if j != k:
                    s.add(Implies(
                        And(sequence[i] == j, sequence[i + 1] == k),
                        friends[k]["start"] >= friends[j]["end"] + travel_times[friends[j]["location"]][friends[k]["location"]]
                    ))

    # Starting from Presidio
    first_meeting = sequence[0]
    for j in range(num_friends):
        s.add(Implies(
            first_meeting == j,
            friends[j]["start"] >= travel_times["Presidio"][friends[j]["location"]]
        ))

    # Maximize number of meetings
    meets = [Bool(f"meets_{friend['name']}") for friend in friends]
    for i, friend in enumerate(friends):
        s.add(meets[i] == (sequence.contains(i)))
    s.maximize(Sum([If(m, 1, 0) for m in meets]))

    # Check if solution exists
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(num_friends):
            idx = model.evaluate(sequence[i]).as_long()
            friend = friends[idx]
            start_val = model.evaluate(friend["start"]).as_long()
            end_val = model.evaluate(friend["end"]).as_long()
            start_hour = 9 + start_val // 60
            start_min = start_val % 60
            end_hour = 9 + end_val // 60
            end_min = end_val % 60
            itinerary.append({
                "action": "meet",
                "person": friend["name"],
                "start_time": f"{start_hour:02d}:{start_min:02d}",
                "end_time": f"{end_hour:02d}:{end_min:02d}",
                "location": friend["location"]
            })
        # Sort by start time
        itinerary.sort(key=lambda x: (int(x["start_time"][:2]), int(x["start_time"][3:5])))
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()