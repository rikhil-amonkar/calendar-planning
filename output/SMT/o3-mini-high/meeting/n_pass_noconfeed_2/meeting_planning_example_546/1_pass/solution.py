from z3 import *
import json

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define friend meeting parameters
    # Times are in minutes after midnight.
    # Kenneth: 21:15-22:00, 30 min meeting, at Richmond District.
    # Lisa: 9:00-16:30, 45 min meeting, at Union Square.
    # Joshua: 12:00-15:15, 15 min meeting, at Financial District.
    # Nancy: 8:00-11:30, 90 min meeting, at Pacific Heights.
    # Andrew: 11:30-20:15, 60 min meeting, at Nob Hill.
    # John: 16:45-21:30, 75 min meeting, at Bayview.
    friends = [
        {"name": "Kenneth", "location": "Richmond District", "avail_start": 21*60+15, "avail_end": 22*60, "duration": 30},
        {"name": "Lisa", "location": "Union Square", "avail_start": 9*60, "avail_end": 16*60+30, "duration": 45},
        {"name": "Joshua", "location": "Financial District", "avail_start": 12*60, "avail_end": 15*60+15, "duration": 15},
        {"name": "Nancy", "location": "Pacific Heights", "avail_start": 8*60, "avail_end": 11*60+30, "duration": 90},
        {"name": "Andrew", "location": "Nob Hill", "avail_start": 11*60+30, "avail_end": 20*60+15, "duration": 60},
        {"name": "John", "location": "Bayview", "avail_start": 16*60+45, "avail_end": 21*60+30, "duration": 75}
    ]
    N = len(friends)
    
    # Define travel times in minutes between locations (as given)
    travel = {
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Bayview"): 21,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Bayview"): 26,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Bayview"): 15,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Bayview"): 19,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Bayview"): 22,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Bayview"): 19,
        ("Bayview", "Embarcadero"): 19,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Union Square"): 17,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Nob Hill"): 20,
    }
    
    # Create an Optimize object from Z3
    opt = Optimize()
    
    # Define decision variables:
    # s[i] = start time of meeting i (in minutes after midnight)
    # order[i] = order (position) in the itinerary (0 means first)
    s = [Int(f"s_{i}") for i in range(N)]
    order_vars = [Int(f"order_{i}") for i in range(N)]
    # t_end represents the overall finish time of all meetings.
    t_end = Int("t_end")
    
    # Add constraints for each meeting's availability and meeting duration
    for i in range(N):
        # Meeting must start no earlier than the friend's available start.
        opt.add(s[i] >= friends[i]["avail_start"])
        # Meeting must finish before the friend's available end.
        opt.add(s[i] + friends[i]["duration"] <= friends[i]["avail_end"])
        # Order variable must be between 0 and N-1.
        opt.add(order_vars[i] >= 0, order_vars[i] < N)
    
    # Ensure a proper permutation of meeting order.
    opt.add(Distinct(order_vars))
    
    # For the meeting that is first in the order, account for travel from Embarcadero (arrival at 9:00 -> 540 minutes)
    for i in range(N):
        loc = friends[i]["location"]
        travel_time = travel[("Embarcadero", loc)]
        opt.add(Implies(order_vars[i] == 0, s[i] >= 540 + travel_time))
    
    # For every pair of different meetings, if meeting i comes before meeting j then
    # meeting j must start after meeting i ends plus the travel time from i's location to j's.
    for i in range(N):
        for j in range(N):
            if i != j:
                loc_i = friends[i]["location"]
                loc_j = friends[j]["location"]
                travel_time = travel[(loc_i, loc_j)]
                opt.add(Implies(order_vars[i] < order_vars[j],
                                s[j] >= s[i] + friends[i]["duration"] + travel_time))
    
    # Define overall finish time as at least every meeting's finish time.
    for i in range(N):
        opt.add(t_end >= s[i] + friends[i]["duration"])
    
    # Objective: minimize the overall finishing time to get the earliest schedule.
    opt.minimize(t_end)
    
    # Solve the constraints
    if opt.check() == sat:
        model = opt.model()
        meetings = []
        schedule = []
        for i in range(N):
            order_val = model.evaluate(order_vars[i]).as_long()
            start_val = model.evaluate(s[i]).as_long()
            end_val = start_val + friends[i]["duration"]
            schedule.append((order_val, friends[i]["name"], friends[i]["location"], start_val, end_val))
        # Sort meetings by the order (ascending)
        schedule.sort(key=lambda x: x[0])
        for _, name, loc, start, end in schedule:
            meetings.append({
                "action": "meet",
                "location": loc,
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        itinerary = {"itinerary": meetings}
        print(json.dumps(itinerary, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()