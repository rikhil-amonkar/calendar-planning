from z3 import *
import json

def format_time(t):
    # Convert integer minutes (since midnight) to HH:MM string in 24-hour format.
    hours = t // 60
    minutes = t % 60
    return f"{hours:02d}:{minutes:02d}"

def main():
    # Friend data: each friend has a meeting location, an available time window (in minutes since midnight)
    # and a minimum meeting duration (in minutes).
    # Times: 9:00AM = 540 minutes; 10:00AM = 600; 11:15AM = 675 etc.
    friends = [
        {"name": "Karen", "location": "Mission District", "avail_start": 14*60+15, "avail_end": 22*60, "duration": 30},
        {"name": "Richard", "location": "Fisherman's Wharf", "avail_start": 14*60+30, "avail_end": 17*60+30, "duration": 30},
        {"name": "Robert", "location": "Presidio", "avail_start": 21*60+45, "avail_end": 22*60+45, "duration": 60},
        {"name": "Joseph", "location": "Union Square", "avail_start": 11*60+45, "avail_end": 14*60+45, "duration": 120},
        {"name": "Helen", "location": "Sunset District", "avail_start": 14*60+45, "avail_end": 20*60+45, "duration": 105},
        {"name": "Elizabeth", "location": "Financial District", "avail_start": 10*60, "avail_end": 12*60+45, "duration": 75},
        {"name": "Kimberly", "location": "Haight-Ashbury", "avail_start": 14*60+15, "avail_end": 17*60+30, "duration": 105},
        {"name": "Ashley", "location": "Russian Hill", "avail_start": 11*60+30, "avail_end": 21*60+30, "duration": 45}
    ]
    
    # Travel times between districts (in minutes), as provided.
    travel = {
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Russian Hill"): 8,
        
        ("Mission District", "Marina District"): 19,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Financial District"): 15,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Russian Hill"): 15,
        
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Russian Hill"): 14,
        
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Russian Hill"): 13,
        
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Mission District"): 25,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Russian Hill"): 24,
        
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Mission District"): 17,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Russian Hill"): 11,
        
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Russian Hill"): 17,
        
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Haight-Ashbury"): 17
    }
    
    # Create a Z3 solver instance.
    solver = Solver()
    n = len(friends)
    
    # For each friend, create two integer decision variables:
    #   - start_var: the meeting start time (in minutes since midnight)
    #   - order_var: the position in the itinerary (an integer between 1 and n)
    for f in friends:
        f["start_var"] = Int("start_" + f["name"])
        f["order_var"] = Int("order_" + f["name"])
        # The meeting must start no earlier than the friend’s available start time and must finish by the available end.
        solver.add(f["start_var"] >= f["avail_start"])
        solver.add(f["start_var"] + f["duration"] <= f["avail_end"])
        # The order position is between 1 and n.
        solver.add(f["order_var"] >= 1, f["order_var"] <= n)
        # For the first meeting in our day, we start at Marina District at 9:00 (540 minutes).
        # Thus, if a friend is scheduled first (order_var == 1), then the meeting cannot start before:
        #   540 + (travel time from Marina District to the friend’s meeting location)
        travel_time = travel[("Marina District", f["location"])]
        solver.add(Implies(f["order_var"] == 1, f["start_var"] >= 540 + travel_time))
    
    # Ensure that each meeting gets a unique order (i.e. the order variables form a permutation).
    solver.add(Distinct([f["order_var"] for f in friends]))
    
    # For any two different meetings, if friend f is scheduled before friend g,
    # then the finish time of f plus the travel time from f.location to g.location must be
    # less than or equal to the start time of g.
    for f in friends:
        for g in friends:
            if f["name"] != g["name"]:
                travel_time_fg = travel[(f["location"], g["location"])]
                solver.add(Implies(f["order_var"] < g["order_var"],
                                   f["start_var"] + f["duration"] + travel_time_fg <= g["start_var"]))
    
    # Check for a feasible schedule.
    if solver.check() == sat:
        model = solver.model()
        schedule = []
        # Extract each meeting’s order, start time, and compute its end time.
        for f in friends:
            order_val = model.evaluate(f["order_var"]).as_long()
            start_val = model.evaluate(f["start_var"]).as_long()
            end_val = start_val + f["duration"]
            schedule.append((order_val, f["name"], start_val, end_val))
        # Sort the meetings by their scheduled order.
        schedule.sort(key=lambda x: x[0])
        
        # Build the itinerary as a list of meeting entries.
        itinerary = []
        for order_val, name, start_val, end_val in schedule:
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": format_time(start_val),
                "end_time": format_time(end_val)
            })
        # Output the itinerary as a JSON-formatted dictionary.
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()