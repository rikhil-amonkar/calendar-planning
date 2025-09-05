from z3 import *
import json

def minutes_to_time_str(m):
    hr = m // 60
    mn = m % 60
    return f"{hr}:{mn:02d}"

def main():
    # Friends and their meeting constraints
    # Times are represented in minutes from midnight.
    friends = [
        {"name": "Stephanie", "location": "Fisherman's Wharf", "avail_start": 15*60+30, "avail_end": 22*60, "min_duration": 30},
        {"name": "Lisa", "location": "Financial District", "avail_start": 10*60+45, "avail_end": 17*60+15, "min_duration": 15},
        {"name": "Melissa", "location": "Russian Hill", "avail_start": 17*60, "avail_end": 21*60+45, "min_duration": 120},
        {"name": "Betty", "location": "Marina District", "avail_start": 10*60+45, "avail_end": 14*60+15, "min_duration": 60},
        {"name": "Sarah", "location": "Richmond District", "avail_start": 16*60+15, "avail_end": 19*60+30, "min_duration": 105},
        {"name": "Daniel", "location": "Pacific Heights", "avail_start": 18*60+30, "avail_end": 21*60+45, "min_duration": 60},
        {"name": "Joshua", "location": "Haight-Ashbury", "avail_start": 9*60, "avail_end": 15*60+30, "min_duration": 15},
        {"name": "Joseph", "location": "Presidio", "avail_start": 7*60, "avail_end": 13*60, "min_duration": 45},
        {"name": "Andrew", "location": "Nob Hill", "avail_start": 19*60+45, "avail_end": 22*60, "min_duration": 105},
        {"name": "John", "location": "The Castro", "avail_start": 13*60+15, "avail_end": 19*60+45, "min_duration": 45},
    ]

    # Define travel times (in minutes) between locations.
    # Each key is a tuple (from_location, to_location)
    travel_times = {
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "The Castro"): 25,

        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "The Castro"): 27,

        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "The Castro"): 20,

        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "The Castro"): 21,

        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "The Castro"): 22,

        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "The Castro"): 16,

        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "The Castro"): 16,

        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "The Castro"): 6,

        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "The Castro"): 21,

        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "The Castro"): 17,

        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Nob Hill"): 16,
    }

    # Create an Optimize object.
    opt = Optimize()
    n = len(friends)
    
    # Decision variables:
    # chosen[i] indicates whether friend i is scheduled.
    chosen = [Bool(f"chosen_{i}") for i in range(n)]
    # s_vars[i] and e_vars[i] denote meeting start and end times (in minutes).
    s_vars = [Int(f"s_{i}") for i in range(n)]
    e_vars = [Int(f"e_{i}") for i in range(n)]
    # order_vars[i] denotes the position in the itinerary (0 means not scheduled).
    order_vars = [Int(f"order_{i}") for i in range(n)]
    
    # total_meetings is the total number of scheduled meetings.
    total_meetings = Int("total_meetings")
    opt.add(total_meetings >= 0, total_meetings <= n)
    opt.add(total_meetings == Sum([If(chosen[i], 1, 0) for i in range(n)]))
    
    # Meeting-specific availability and duration constraints.
    for i, f in enumerate(friends):
        # If friend is chosen, then ensure meeting is scheduled within the available window
        # and lasts at least the required minimum duration.
        opt.add(
            If(chosen[i],
               And(s_vars[i] >= f["avail_start"],
                   e_vars[i] <= f["avail_end"],
                   e_vars[i] - s_vars[i] >= f["min_duration"]),
               order_vars[i] == 0)
        )
        # If chosen, assign an order between 1 and total_meetings.
        opt.add(Implies(chosen[i], And(order_vars[i] >= 1, order_vars[i] <= total_meetings)))
    
    # Ensure unique ordering for chosen meetings.
    for i in range(n):
        for j in range(i+1, n):
            opt.add(Implies(And(chosen[i], chosen[j]), order_vars[i] != order_vars[j]))
    
    # Enforce that for every k from 1 to n, if k <= total_meetings then some meeting is assigned order k.
    for k in range(1, n+1):
        opt.add(Implies(total_meetings >= k, Or([order_vars[i] == k for i in range(n)])))
    
    # Travel constraints:
    # For the first meeting (order == 1), the meeting must start no earlier than 
    # arrival time (9:00 AM = 540) plus travel time from Embarcadero.
    for i, f in enumerate(friends):
        travel_from_start = travel_times[("Embarcadero", f["location"])]
        opt.add(Implies(And(chosen[i], order_vars[i] == 1), s_vars[i] >= 540 + travel_from_start))
    
    # For consecutive meetings, ensure that the later meeting starts after the earlier meeting
    # finishes plus travel time between the two meeting locations.
    for i in range(n):
        for j in range(n):
            if i != j:
                travel_ij = travel_times[(friends[i]["location"], friends[j]["location"])]
                opt.add(Implies(And(chosen[i], chosen[j], order_vars[j] == order_vars[i] + 1),
                                s_vars[j] >= e_vars[i] + travel_ij))
    
    # Optional: Domain constraints on meeting times.
    for i in range(n):
        opt.add(s_vars[i] >= 0, e_vars[i] >= 0, s_vars[i] <= 1440, e_vars[i] <= 1440)
    
    # Objective: maximize the total number of meetings scheduled.
    h = opt.maximize(total_meetings)
    
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        scheduled = []
        for i in range(n):
            if is_true(model.evaluate(chosen[i])):
                order_val = model.evaluate(order_vars[i]).as_long()
                start_val = model.evaluate(s_vars[i]).as_long()
                end_val = model.evaluate(e_vars[i]).as_long()
                scheduled.append((order_val, friends[i]["location"], friends[i]["name"], start_val, end_val))
        scheduled.sort(key=lambda x: x[0])
        for order_val, location, name, start_val, end_val in scheduled:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": minutes_to_time_str(start_val),
                "end_time": minutes_to_time_str(end_val)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))
        
if __name__ == "__main__":
    main()