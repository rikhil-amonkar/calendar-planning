from z3 import *
import json

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Friend meeting data: available time windows in minutes from midnight and minimum meeting duration
    # Times: 9:00 = 540, etc.
    # Data: name, location, avail_start, avail_end, duration (minutes)
    friends = [
        {"name": "Elizabeth", "location": "Mission District", "avail_start": 630, "avail_end": 1200, "duration": 90},
        {"name": "David", "location": "Union Square", "avail_start": 915, "avail_end": 1140, "duration": 45},
        {"name": "Sandra", "location": "Pacific Heights", "avail_start": 420, "avail_end": 1200, "duration": 120},
        {"name": "Thomas", "location": "Bayview", "avail_start": 1170, "avail_end": 1230, "duration": 30},
        {"name": "Robert", "location": "Fisherman's Wharf", "avail_start": 600, "avail_end": 900, "duration": 15},
        {"name": "Kenneth", "location": "Marina District", "avail_start": 645, "avail_end": 780, "duration": 45},
        {"name": "Melissa", "location": "Richmond District", "avail_start": 1095, "avail_end": 1200, "duration": 15},
        {"name": "Kimberly", "location": "Sunset District", "avail_start": 615, "avail_end": 1095, "duration": 105},
        {"name": "Amanda", "location": "Golden Gate Park", "avail_start": 465, "avail_end": 1125, "duration": 15}
    ]
    n_friends = len(friends)  # 9 friends

    # Travel times (in minutes) between locations
    travel = {
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Bayview"): 14,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Golden Gate Park"): 17,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Golden Gate Park"): 22,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Bayview"): 22,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Mission District"): 13,
        ("Bayview", "Union Square"): 18,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Sunset District"): 23,
        ("Bayview", "Golden Gate Park"): 22,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Golden Gate Park"): 18,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Bayview"): 27,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Mission District"): 25,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Sunset District"): 10
    }

    max_slots = n_friends  # maximum possible meetings

    opt = Optimize()

    # Create decision variables: for each slot, we decide which meeting (friend index) is scheduled.
    # -1 means the slot is not used.
    meetings = [Int(f"meeting_{i}") for i in range(max_slots)]
    starts = [Int(f"start_{i}") for i in range(max_slots)]

    # Each meeting slot decision variable must be in the domain [-1, n_friends-1]
    for i in range(max_slots):
        opt.add(meetings[i] >= -1, meetings[i] <= n_friends - 1)
        opt.add(starts[i] >= 0, starts[i] <= 1440)

    # Enforce contiguous assignment of meetings: once a slot is empty (-1), all subsequent slots must be empty.
    for i in range(max_slots - 1):
        opt.add(Implies(meetings[i] == -1, meetings[i+1] == -1))

    # Enforce that if two slots are scheduled, they refer to distinct friends.
    for i in range(max_slots):
        for j in range(i+1, max_slots):
            opt.add(Implies(And(meetings[i] != -1, meetings[j] != -1), meetings[i] != meetings[j]))

    # Add constraints for each slot based on the selected friend.
    for i in range(max_slots):
        for j in range(n_friends):
            # If slot i is assigned friend j, the meeting must occur within the friend's available time
            opt.add(Implies(meetings[i] == j, starts[i] >= friends[j]["avail_start"]))
            opt.add(Implies(meetings[i] == j, starts[i] + friends[j]["duration"] <= friends[j]["avail_end"]))
            # For the first meeting, ensure arrival from starting location "Haight-Ashbury" at 9:00 (540 minutes)
            if i == 0:
                travel_time = travel[("Haight-Ashbury", friends[j]["location"])]
                opt.add(Implies(meetings[0] == j, starts[0] >= 540 + travel_time))

    # Add travel constraints between consecutive scheduled meetings.
    for i in range(1, max_slots):
        for prev in range(n_friends):
            for curr in range(n_friends):
                travel_time = travel[(friends[prev]["location"], friends[curr]["location"])]
                # If slot i-1 is friend 'prev' and slot i is friend 'curr', then the meeting in slot i must start
                # after the previous meeting ends plus travel time.
                opt.add(Implies(And(meetings[i-1] == prev, meetings[i] == curr),
                                starts[i] >= starts[i-1] + friends[prev]["duration"] + travel_time))

    # Define the objective: maximize the number of scheduled meetings.
    scheduled_count = Sum([If(meetings[i] != -1, 1, 0) for i in range(max_slots)])
    opt.maximize(scheduled_count)

    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for i in range(max_slots):
            meeting_val = model.evaluate(meetings[i]).as_long()
            if meeting_val == -1:
                break
            friend = friends[meeting_val]
            start_time = model.evaluate(starts[i]).as_long()
            end_time = start_time + friend["duration"]
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()