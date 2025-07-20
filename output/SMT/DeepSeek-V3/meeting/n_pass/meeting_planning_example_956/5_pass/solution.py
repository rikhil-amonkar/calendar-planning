from z3 import *
import json

def solve_scheduling():
    s = Optimize()

    # Friends data: name -> {location, start_time, end_time, min_duration}
    friends = {
        "William": {"location": "Alamo Square", "start": "15:15", "end": "17:15", "duration": 60},
        "Joshua": {"location": "Richmond District", "start": "7:00", "end": "20:00", "duration": 15},
        "Joseph": {"location": "Financial District", "start": "11:15", "end": "13:30", "duration": 15},
        "David": {"location": "Union Square", "start": "16:45", "end": "19:15", "duration": 45},
        "Brian": {"location": "Fisherman's Wharf", "start": "13:45", "end": "20:45", "duration": 105},
        "Karen": {"location": "Marina District", "start": "11:30", "end": "18:30", "duration": 15},
        "Anthony": {"location": "Haight-Ashbury", "start": "7:15", "end": "10:30", "duration": 30},
        "Matthew": {"location": "Mission District", "start": "17:15", "end": "19:15", "duration": 120},
        "Helen": {"location": "Pacific Heights", "start": "8:00", "end": "12:00", "duration": 75},
        "Jeffrey": {"location": "Golden Gate Park", "start": "19:00", "end": "21:30", "duration": 60}
    }

    # Complete travel times between all locations (in minutes)
    travel_times = {
        "The Castro": {
            "Alamo Square": 8, "Richmond District": 16, "Financial District": 21,
            "Union Square": 19, "Fisherman's Wharf": 24, "Marina District": 21,
            "Haight-Ashbury": 6, "Mission District": 7, "Pacific Heights": 16,
            "Golden Gate Park": 11
        },
        "Alamo Square": {
            "The Castro": 8, "Richmond District": 11, "Financial District": 17,
            "Union Square": 14, "Fisherman's Wharf": 19, "Marina District": 15,
            "Haight-Ashbury": 5, "Mission District": 10, "Pacific Heights": 10,
            "Golden Gate Park": 9
        },
        "Richmond District": {
            "The Castro": 16, "Alamo Square": 11, "Financial District": 22,
            "Union Square": 21, "Fisherman's Wharf": 18, "Marina District": 9,
            "Haight-Ashbury": 10, "Mission District": 20, "Pacific Heights": 10,
            "Golden Gate Park": 9
        },
        "Financial District": {
            "The Castro": 21, "Alamo Square": 17, "Richmond District": 22,
            "Union Square": 9, "Fisherman's Wharf": 10, "Marina District": 15,
            "Haight-Ashbury": 19, "Mission District": 17, "Pacific Heights": 13,
            "Golden Gate Park": 23
        },
        "Union Square": {
            "The Castro": 19, "Alamo Square": 14, "Richmond District": 21,
            "Financial District": 9, "Fisherman's Wharf": 15, "Marina District": 18,
            "Haight-Ashbury": 18, "Mission District": 14, "Pacific Heights": 15,
            "Golden Gate Park": 22
        },
        "Fisherman's Wharf": {
            "The Castro": 24, "Alamo Square": 19, "Richmond District": 18,
            "Financial District": 10, "Union Square": 13, "Marina District": 9,
            "Haight-Ashbury": 22, "Mission District": 22, "Pacific Heights": 12,
            "Golden Gate Park": 25
        },
        "Marina District": {
            "The Castro": 21, "Alamo Square": 15, "Richmond District": 9,
            "Financial District": 17, "Union Square": 16, "Fisherman's Wharf": 10,
            "Haight-Ashbury": 16, "Mission District": 20, "Pacific Heights": 7,
            "Golden Gate Park": 18
        },
        "Haight-Ashbury": {
            "The Castro": 6, "Alamo Square": 5, "Richmond District": 10,
            "Financial District": 21, "Union Square": 19, "Fisherman's Wharf": 23,
            "Marina District": 17, "Mission District": 11, "Pacific Heights": 12,
            "Golden Gate Park": 7
        },
        "Mission District": {
            "The Castro": 7, "Alamo Square": 10, "Richmond District": 20,
            "Financial District": 17, "Union Square": 15, "Fisherman's Wharf": 22,
            "Marina District": 19, "Haight-Ashbury": 12, "Pacific Heights": 16,
            "Golden Gate Park": 17
        },
        "Pacific Heights": {
            "The Castro": 16, "Alamo Square": 10, "Richmond District": 12,
            "Financial District": 13, "Union Square": 12, "Fisherman's Wharf": 13,
            "Marina District": 6, "Haight-Ashbury": 11, "Mission District": 15,
            "Golden Gate Park": 15
        },
        "Golden Gate Park": {
            "The Castro": 11, "Alamo Square": 9, "Richmond District": 7,
            "Financial District": 23, "Union Square": 22, "Fisherman's Wharf": 25,
            "Marina District": 18, "Haight-Ashbury": 7, "Mission District": 17,
            "Pacific Heights": 15
        }
    }

    # Helper functions to convert between time strings and minutes
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Create variables for each meeting's start and end times
    meeting_starts = {name: Int(f"start_{name}") for name in friends}
    meeting_ends = {name: Int(f"end_{name}") for name in friends}

    # Variables to track if we meet each friend
    meet_friend = {name: Bool(f"meet_{name}") for name in friends}

    # Add constraints for each friend's availability and duration
    for name, info in friends.items():
        start_min = time_to_minutes(info["start"])
        end_min = time_to_minutes(info["end"])
        duration = info["duration"]

        # If we meet this friend, enforce time constraints
        s.add(Implies(meet_friend[name], 
                     And(meeting_starts[name] >= start_min,
                         meeting_ends[name] <= end_min,
                         meeting_ends[name] == meeting_starts[name] + duration)))

    # Create a total order of meetings to ensure proper sequencing
    meeting_order = {name: Int(f"order_{name}") for name in friends}
    for name in friends:
        s.add(meeting_order[name] >= 0)
        s.add(Implies(meet_friend[name], meeting_order[name] >= 1))

    # Ensure meetings are properly ordered with travel times
    for i in friends:
        for j in friends:
            if i != j:
                loc_i = friends[i]["location"]
                loc_j = friends[j]["location"]
                travel_time = travel_times[loc_i].get(loc_j, 0)
                
                s.add(Implies(And(meet_friend[i], meet_friend[j], meeting_order[i] + 1 == meeting_order[j]),
                      meeting_ends[i] + travel_time <= meeting_starts[j]))

    # Starting at The Castro at 9:00 AM
    # First meeting must be after accounting for travel from The Castro
    for name in friends:
        loc = friends[name]["location"]
        travel_time = travel_times["The Castro"][loc]
        s.add(Implies(And(meet_friend[name], meeting_order[name] == 1),
                     meeting_starts[name] >= time_to_minutes("9:00") + travel_time))

    # Maximize the number of friends met
    s.maximize(Sum([If(meet_friend[name], 1, 0) for name in friends]))

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in friends:
            if is_true(model[meet_friend[name]]):
                start = model[meeting_starts[name]].as_long()
                end = model[meeting_ends[name]].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid schedule found"}

# Get the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))