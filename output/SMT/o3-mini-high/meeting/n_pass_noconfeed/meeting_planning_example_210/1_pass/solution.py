from z3 import *
import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Initialize the Z3 optimizer
    opt = Optimize()
    
    # Friend meeting details
    # Times are in minutes since midnight.
    # Emily: available from 16:15 (975) to 21:00 (1260), minimum meeting duration 105 minutes, at Presidio.
    # Joseph: available from 17:15 (1035) to 22:00 (1320), minimum meeting duration 120 minutes, at Richmond District.
    # Melissa: available from 15:45 (945) to 21:45 (1305), minimum meeting duration 75 minutes, at Financial District.
    friends = [
        {"name": "Emily", "location": "Presidio", "avail_start": 16 * 60 + 15, "avail_end": 21 * 60, "min_duration": 105},
        {"name": "Joseph", "location": "Richmond District", "avail_start": 17 * 60 + 15, "avail_end": 22 * 60, "min_duration": 120},
        {"name": "Melissa", "location": "Financial District", "avail_start": 15 * 60 + 45, "avail_end": 21 * 60 + 45, "min_duration": 75}
    ]
    
    num_friends = len(friends)
    
    # Starting condition: Arrive at Fisherman's Wharf at 9:00AM (540 minutes)
    start_time = 9 * 60
    start_location = "Fisherman's Wharf"
    
    # Travel times (in minutes)
    travel_times = {
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Financial District"): 23,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Financial District"): 22,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Richmond District"): 21
    }
    
    # Create SMT variables for each meeting:
    # S[i]: start time, E[i]: end time, order_vars[i]: order position (1,2,3) in the itinerary.
    S = [Int(f"S_{i}") for i in range(num_friends)]
    E = [Int(f"E_{i}") for i in range(num_friends)]
    order_vars = [Int(f"order_{i}") for i in range(num_friends)]
    
    # Each order variable must be in {1,2,3} and all different.
    for o in order_vars:
        opt.add(Or(o == 1, o == 2, o == 3))
    opt.add(Distinct(order_vars))
    
    # Add constraints for each meeting's available window and minimum duration.
    for i in range(num_friends):
        friend = friends[i]
        opt.add(S[i] >= friend["avail_start"])
        opt.add(E[i] <= friend["avail_end"])
        opt.add(E[i] - S[i] >= friend["min_duration"])
    
    # Constraint: For the meeting that is scheduled first, account for travel from Fisherman's Wharf.
    for i in range(num_friends):
        friend = friends[i]
        travel_from_start = travel_times[(start_location, friend["location"])]
        opt.add(Implies(order_vars[i] == 1, start_time + travel_from_start <= S[i]))
    
    # Constraint: Order the meetings such that if meeting i comes before meeting j, 
    # then allow enough travel time between the locations.
    for i in range(num_friends):
        for j in range(num_friends):
            if i != j:
                loc_i = friends[i]["location"]
                loc_j = friends[j]["location"]
                travel_ij = travel_times[(loc_i, loc_j)]
                opt.add(Implies(order_vars[i] < order_vars[j], E[i] + travel_ij <= S[j]))
    
    # Optional: Optimize by minimizing the finishing time of the last meeting.
    last_finish = Int("last_finish")
    for i in range(num_friends):
        opt.add(last_finish >= E[i])
    opt.minimize(last_finish)
    
    # Solve the constraints
    if opt.check() == sat:
        model = opt.model()
        # Extract meeting information from the model.
        meetings = []
        for i in range(num_friends):
            meetings.append({
                "person": friends[i]["name"],
                "location": friends[i]["location"],
                "start": model[S[i]].as_long(),
                "end": model[E[i]].as_long(),
                "order": model[order_vars[i]].as_long()
            })
        # Sort meetings by their scheduled order.
        meetings = sorted(meetings, key=lambda x: x["order"])
        
        # Build the itinerary list with formatted times.
        itinerary = []
        for meet in meetings:
            itinerary.append({
                "action": "meet",
                "location": meet["location"],
                "person": meet["person"],
                "start_time": format_time(meet["start"]),
                "end_time": format_time(meet["end"])
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        # In case no schedule could be found, return an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()