from z3 import *

def main():
    # Define location indices
    locations = {
        "Haight-Ashbury": 0,
        "Mission District": 1,
        "Union Square": 2,
        "Pacific Heights": 3,
        "Bayview": 4,
        "Fisherman's Wharf": 5,
        "Marina District": 6,
        "Richmond District": 7,
        "Sunset District": 8,
        "Golden Gate Park": 9
    }
    
    # Build travel time matrix (10x10)
    travel = [[0] * 10 for _ in range(10)]
    
    travel_text = """
Haight-Ashbury to Mission District: 11.
Haight-Ashbury to Union Square: 19.
Haight-Ashbury to Pacific Heights: 12.
Haight-Ashbury to Bayview: 18.
Haight-Ashbury to Fisherman's Wharf: 23.
Haight-Ashbury to Marina District: 17.
Haight-Ashbury to Richmond District: 10.
Haight-Ashbury to Sunset District: 15.
Haight-Ashbury to Golden Gate Park: 7.
Mission District to Haight-Ashbury: 12.
Mission District to Union Square: 15.
Mission District to Pacific Heights: 16.
Mission District to Bayview: 14.
Mission District to Fisherman's Wharf: 22.
Mission District to Marina District: 19.
Mission District to Richmond District: 20.
Mission District to Sunset District: 24.
Mission District to Golden Gate Park: 17.
Union Square to Haight-Ashbury: 18.
Union Square to Mission District: 14.
Union Square to Pacific Heights: 15.
Union Square to Bayview: 15.
Union Square to Fisherman's Wharf: 15.
Union Square to Marina District: 18.
Union Square to Richmond District: 20.
Union Square to Sunset District: 27.
Union Square to Golden Gate Park: 22.
Pacific Heights to Haight-Ashbury: 11.
Pacific Heights to Mission District: 15.
Pacific Heights to Union Square: 12.
Pacific Heights to Bayview: 22.
Pacific Heights to Fisherman's Wharf: 13.
Pacific Heights to Marina District: 6.
Pacific Heights to Richmond District: 12.
Pacific Heights to Sunset District: 21.
Pacific Heights to Golden Gate Park: 15.
Bayview to Haight-Ashbury: 19.
Bayview to Mission District: 13.
Bayview to Union Square: 18.
Bayview to Pacific Heights: 23.
Bayview to Fisherman's Wharf: 25.
Bayview to Marina District: 27.
Bayview to Richmond District: 25.
Bayview to Sunset District: 23.
Bayview to Golden Gate Park: 22.
Fisherman's Wharf to Haight-Ashbury: 22.
Fisherman's Wharf to Mission District: 22.
Fisherman's Wharf to Union Square: 13.
Fisherman's Wharf to Pacific Heights: 12.
Fisherman's Wharf to Bayview: 26.
Fisherman's Wharf to Marina District: 9.
Fisherman's Wharf to Richmond District: 18.
Fisherman's Wharf to Sunset District: 27.
Fisherman's Wharf to Golden Gate Park: 25.
Marina District to Haight-Ashbury: 16.
Marina District to Mission District: 20.
Marina District to Union Square: 16.
Marina District to Pacific Heights: 7.
Marina District to Bayview: 27.
Marina District to Fisherman's Wharf: 10.
Marina District to Richmond District: 11.
Marina District to Sunset District: 19.
Marina District to Golden Gate Park: 18.
Richmond District to Haight-Ashbury: 10.
Richmond District to Mission District: 20.
Richmond District to Union Square: 21.
Richmond District to Pacific Heights: 10.
Richmond District to Bayview: 27.
Richmond District to Fisherman's Wharf: 18.
Richmond District to Marina District: 9.
Richmond District to Sunset District: 11.
Richmond District to Golden Gate Park: 9.
Sunset District to Haight-Ashbury: 15.
Sunset District to Mission District: 25.
Sunset District to Union Square: 30.
Sunset District to Pacific Heights: 21.
Sunset District to Bayview: 22.
Sunset District to Fisherman's Wharf: 29.
Sunset District to Marina District: 21.
Sunset District to Richmond District: 12.
Sunset District to Golden Gate Park: 11.
Golden Gate Park to Haight-Ashbury: 7.
Golden Gate Park to Mission District: 17.
Golden Gate Park to Union Square: 22.
Golden Gate Park to Pacific Heights: 16.
Golden Gate Park to Bayview: 23.
Golden Gate Park to Fisherman's Wharf: 24.
Golden Gate Park to Marina District: 16.
Golden Gate Park to Richmond District: 7.
Golden Gate Park to Sunset District: 10.
"""
    lines = travel_text.strip().split('\n')
    for line in lines:
        line = line.strip()
        if not line:
            continue
        if line.endswith('.'):
            line = line[:-1]
        parts = line.split(' to ')
        if len(parts) < 2:
            continue
        from_loc_str = parts[0].strip()
        rest = parts[1].strip()
        parts2 = rest.split(':')
        if len(parts2) < 2:
            continue
        to_loc_str = parts2[0].strip()
        time_val = int(parts2[1].strip())
        from_idx = locations[from_loc_str]
        to_idx = locations[to_loc_str]
        travel[from_idx][to_idx] = time_val

    # Friend data: index 1 to 9
    friends = [
        # Elizabeth: Mission District (index1)
        {"name": "Elizabeth", "loc": 1, "start_avail": 630, "end_avail": 1200, "min_dur": 90},
        # David: Union Square (index2)
        {"name": "David", "loc": 2, "start_avail": 915, "end_avail": 1140, "min_dur": 45},
        # Sandra: Pacific Heights (index3)
        {"name": "Sandra", "loc": 3, "start_avail": 420, "end_avail": 1200, "min_dur": 120},
        # Thomas: Bayview (index4)
        {"name": "Thomas", "loc": 4, "start_avail": 1170, "end_avail": 1230, "min_dur": 30},
        # Robert: Fisherman's Wharf (index5)
        {"name": "Robert", "loc": 5, "start_avail": 600, "end_avail": 900, "min_dur": 15},
        # Kenneth: Marina District (index6)
        {"name": "Kenneth", "loc": 6, "start_avail": 645, "end_avail": 780, "min_dur": 45},
        # Melissa: Richmond District (index7)
        {"name": "Melissa", "loc": 7, "start_avail": 1095, "end_avail": 1200, "min_dur": 15},
        # Kimberly: Sunset District (index8)
        {"name": "Kimberly", "loc": 8, "start_avail": 615, "end_avail": 1095, "min_dur": 105},
        # Amanda: Golden Gate Park (index9)
        {"name": "Amanda", "loc": 9, "start_avail": 465, "end_avail": 1125, "min_dur": 15}
    ]
    
    # Create Z3 variables
    s = Optimize()
    
    # Dummy meeting (index0)
    time0 = 540  # 9:00 AM in minutes from midnight
    do0 = True
    order0 = 0
    
    # For friends 1 to 9: index 0 to 8 in friends list, but we index variables from 1 to 9.
    do = [None] * 10  # 0 to 9, but 0 is dummy (do0=True)
    time = [None] * 10
    order = [None] * 10
    
    for i in range(1, 10):
        do[i] = Bool(f'do_{i}')
        time[i] = Int(f'time_{i}')
        order[i] = Int(f'order_{i}')
    
    # Constraints list
    constraints = []
    
    # Dummy meeting fixed
    constraints.append(time[0] == time0)  # though we won't use time[0] as a variable, we set it for consistency
    # But we don't have Z3 variables for the dummy, so we just use the value when needed.
    
    # For each friend i (1..9)
    for idx in range(1, 10):
        i = idx
        friend = friends[i-1]  # because friends[0] corresponds to friend1
        # Constraint: if do_i is True, then time_i within window and duration
        constraints.append(Implies(do[i], 
                                  And(time[i] >= friend["start_avail"], 
                                      time[i] + friend["min_dur"] <= friend["end_avail"])))
        # Constraint: if do_i and order_i==1, then time_i >= 540 + travel[0][friend_loc]
        friend_loc = friend["loc"]
        constraints.append(Implies(And(do[i], order[i] == 1),
                                  time[i] >= time0 + travel[0][friend_loc]))
        
        # Constraint: if do_i, then order_i between 1 and 9
        constraints.append(Implies(do[i], And(order[i] >= 1, order[i] <= 9)))
        
    # Constraints for distinct orders for done meetings
    for i in range(1, 10):
        for j in range(i+1, 10):
            constraints.append(Implies(And(do[i], do[j]), order[i] != order[j]))
    
    # Constraints for travel from a meeting j to meeting i (if j is the predecessor of i)
    for i in range(1, 10):
        for j in range(1, 10):
            if i == j:
                continue
            # If both do_i and do_j are true, and order_j = order_i - 1, then time_i >= time_j + min_dur_j + travel[loc_j][loc_i]
            friend_i = friends[i-1]
            friend_j = friends[j-1]
            loc_i = friend_i["loc"]
            loc_j = friend_j["loc"]
            constraints.append(
                Implies(And(do[i], do[j], order[j] == order[i] - 1),
                time[i] >= time[j] + friend_j["min_dur"] + travel[loc_j][loc_i]
            )
    
    # Constraint: for each done meeting i with order_i>=2, there must be a done meeting j (j != i) such that order_j = order_i - 1
    for i in range(1, 10):
        # Create a list of conditions for j in 1..9, j != i, that (do_j and order_j == order_i-1)
        conds = []
        for j in range(1, 10):
            if j == i:
                continue
            conds.append(And(do[j], order[j] == order[i] - 1))
        if conds:
            constraints.append(
                Implies(And(do[i], order[i] >= 2), Or(conds))
        else:
            # Only one meeting? then if i is done and order_i>=2, we require False (but there is no j) -> so we must avoid this.
            pass
    
    # Objective: maximize the number of done meetings
    obj = Sum([If(do[i], 1, 0) for i in range(1,10)])
    s.maximize(obj)
    
    # Add constraints
    s.add(constraints)
    
    # Solve
    if s.check() == sat:
        m = s.model()
        # Extract the meetings that are done and their details
        itinerary = []
        for i in range(1, 10):
            if is_true(m[do[i]]):
                start_min = m[time[i]].as_long()
                friend = friends[i-1]
                dur = friend["min_dur"]
                end_min = start_min + dur
                # Convert to HH:MM
                start_hour = start_min // 60
                start_minute = start_min % 60
                end_hour = end_min // 60
                end_minute = end_min % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friend["name"],
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort by start time? But we have the sequence order. We can sort by the order_i value? But we don't extract order_i? We don't need to output in sequence order? 
        # The problem does not specify the order of the itinerary list. But the example is a list. We'll output in the order of the friends list? 
        # But to show the schedule, we can sort by start time.
        itinerary.sort(key=lambda x: x["start_time"])
        # Output as JSON
        print('SOLUTION:')
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print("No solution found")

if __name__ == "__main__":
    main()