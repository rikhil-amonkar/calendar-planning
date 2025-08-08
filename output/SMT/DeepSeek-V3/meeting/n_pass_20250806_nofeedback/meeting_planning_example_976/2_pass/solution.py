from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define travel times (in minutes) between locations
    travel_times = {
        ("Embarcadero", "Bayview"): 21,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Marina District"): 12,
        ("Bayview", "Embarcadero"): 19,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Nob Hill"): 20,
        ("Bayview", "Presidio"): 32,
        ("Bayview", "Union Square"): 18,
        ("Bayview", "The Castro"): 19,
        ("Bayview", "North Beach"): 22,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Marina District"): 27,
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Bayview"): 20,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Chinatown", "Marina District"): 12,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Marina District"): 15,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Bayview"): 19,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Marina District"): 11,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Marina District"): 11,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "The Castro"): 17,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Marina District"): 18,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Bayview"): 19,
        ("The Castro", "Chinatown"): 22,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Marina District"): 21,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Bayview"): 25,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "The Castro"): 23,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Marina District"): 9,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Fisherman's Wharf"): 10,
    }

    # Friends' availability and constraints
    friends = {
        "Matthew": {"location": "Bayview", "start": (19, 15), "end": (22, 0), "duration": 120},
        "Karen": {"location": "Chinatown", "start": (19, 15), "end": (21, 15), "duration": 90},
        "Sarah": {"location": "Alamo Square", "start": (20, 0), "end": (21, 45), "duration": 105},
        "Jessica": {"location": "Nob Hill", "start": (16, 30), "end": (18, 45), "duration": 120},
        "Stephanie": {"location": "Presidio", "start": (7, 30), "end": (10, 15), "duration": 60},
        "Mary": {"location": "Union Square", "start": (16, 45), "end": (21, 30), "duration": 60},
        "Charles": {"location": "The Castro", "start": (16, 30), "end": (22, 0), "duration": 105},
        "Nancy": {"location": "North Beach", "start": (14, 45), "end": (20, 0), "duration": 15},
        "Thomas": {"location": "Fisherman's Wharf", "start": (13, 30), "end": (19, 0), "duration": 30},
        "Brian": {"location": "Marina District", "start": (12, 15), "end": (18, 0), "duration": 60},
    }

    # Convert times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to time string
    def minutes_to_time(m):
        total = m + 540
        h = total // 60
        m = total % 60
        return f"{h:02d}:{m:02d}"

    # Create variables for each meeting
    meetings = {}
    met = {}  # Binary variable indicating if the friend is met
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        met[name] = Bool(f"met_{name}")
        meetings[name] = {"start": start, "end": end, "location": friends[name]["location"], "met": met[name]}
        # Constraints: if met, meeting must be within friend's availability
        s.add(Implies(met[name], start >= time_to_minutes(*friends[name]["start"])))
        s.add(Implies(met[name], end <= time_to_minutes(*friends[name]["end"])))
        s.add(Implies(met[name], end - start >= friends[name]["duration"]))
        s.add(Implies(met[name], start >= 0))  # Cannot start before 9:00 AM

    # Order constraints: ensure travel time between meetings is accounted for
    # We'll add constraints that for any two meetings, if both are met, they don't overlap considering travel time
    names = list(friends.keys())
    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            name1 = names[i]
            name2 = names[j]
            loc1 = meetings[name1]["location"]
            loc2 = meetings[name2]["location"]
            travel = travel_times.get((loc1, loc2), 0)
            # Either meeting1 is before meeting2 or vice versa, or at least one is not met
            s.add(Or(
                Not(met[name1]),
                Not(met[name2]),
                meetings[name1]["end"] + travel <= meetings[name2]["start"],
                meetings[name2]["end"] + travel_times.get((loc2, loc1), 0) <= meetings[name1]["start"]
            ))

    # Maximize the number of friends met
    s.maximize(Sum([If(met[name], 1, 0) for name in friends]))

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for name in friends:
            if m[met[name]]:
                start = m[meetings[name]["start"]].as_long()
                end = m[meetings[name]["end"]].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end),
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling()
print("SOLUTION:")
print(json.dumps(solution, indent=2))