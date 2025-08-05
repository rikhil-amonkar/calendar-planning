from z3 import *
import json

def main():
    # Define locations
    locations = [
        "Haight-Ashbury",
        "Mission District",
        "Union Square",
        "Pacific Heights",
        "Bayview",
        "Fisherman's Wharf",
        "Marina District",
        "Richmond District",
        "Sunset District",
        "Golden Gate Park"
    ]
    
    # Build travel time dictionary from provided data
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
    travel_dict = {}
    lines = travel_text.strip().split('\n')
    for line in lines:
        if not line.strip():
            continue
        parts = line.split(':')
        if len(parts) < 2:
            continue
        route_str = parts[0].strip()
        time_str = parts[1].strip().rstrip('.').strip()
        try:
            time_val = int(time_str)
        except:
            continue
        places = route_str.split(' to ')
        if len(places) != 2:
            continue
        from_place = places[0].strip()
        to_place = places[1].strip()
        travel_dict[(from_place, to_place)] = time_val

    # Create a 10x10 travel_time matrix
    n_locations = len(locations)
    travel_time = [[0] * n_locations for _ in range(n_locations)]
    for i in range(n_locations):
        for j in range(n_locations):
            if i == j:
                travel_time[i][j] = 0
            else:
                key = (locations[i], locations[j])
                if key in travel_dict:
                    travel_time[i][j] = travel_dict[key]
                else:
                    travel_time[i][j] = 1000000  # a large number if not found (should not happen)

    # Define friends and their constraints
    friends = [
        # (name, district, (start_h, start_m), (end_h, end_m), min_duration_minutes)
        ("Elizabeth", "Mission District", (10, 30), (20, 0), 90),
        ("David", "Union Square", (15, 15), (19, 0), 45),
        ("Sandra", "Pacific Heights", (7, 0), (20, 0), 120),
        ("Thomas", "Bayview", (19, 30), (20, 30), 30),
        ("Robert", "Fisherman's Wharf", (10, 0), (15, 0), 15),
        ("Kenneth", "Marina District", (10, 45), (13, 0), 45),
        ("Melissa", "Richmond District", (18, 15), (20, 0), 15),
        ("Kimberly", "Sunset District", (10, 15), (18, 15), 105),
        ("Amanda", "Golden Gate Park", (7, 45), (18, 45), 15)
    ]
    
    # Map district names to indices in the locations list
    district_to_index = {district: idx for idx, district in enumerate(locations)}
    friend_district_indices = [district_to_index[f[1]] for f in friends]
    
    # Convert availability times to minutes from midnight
    def time_to_minutes(h, m):
        return h * 60 + m

    available_start = [time_to_minutes(f[2][0], f[2][1]) for f in friends]
    available_end = [time_to_minutes(f[3][0], f[3][1]) for f in friends]
    min_duration = [f[4] for f in friends]
    
    n_friends = len(friends)
    
    # Create Z3 solver
    s = Solver()
    
    # Decision variables
    meet = [Bool(f'meet_{i}') for i in range(n_friends)]
    position = [Int(f'position_{i}') for i in range(n_friends)]
    start = [Int(f'start_{i}') for i in range(n_friends)]
    end = [Int(f'end_{i}') for i in range(n_friends)]
    
    # Constraints for each friend
    for i in range(n_friends):
        # If we meet friend i, enforce time window and duration
        s.add(Implies(meet[i], start[i] >= available_start[i]))
        s.add(Implies(meet[i], end[i] <= available_end[i]))
        s.add(Implies(meet[i], end[i] - start[i] >= min_duration[i]))
        s.add(Implies(meet[i], position[i] >= 0))
        s.add(Implies(meet[i], position[i] < n_friends))
        s.add(Implies(meet[i], start[i] >= 0))
        s.add(Implies(meet[i], end[i] <= 24*60))  # within the day
    
    # At least one meeting at position 0
    s.add(Or([And(meet[i], position[i] == 0) for i in range(n_friends)]))
    
    # Distinct positions for met friends
    for i in range(n_friends):
        for j in range(i+1, n_friends):
            s.add(Implies(And(meet[i], meet[j]), position[i] != position[j]))
    
    # For each met friend at position>=1, there must be a friend at position-1
    for i in range(n_friends):
        other_friends = [j for j in range(n_friends) if j != i]
        s.add(Implies(And(meet[i], position[i] >= 1),
                      Or([And(meet[j], position[j] == position[i] - 1) for j in other_friends])))
    
    # Travel constraints for first meeting (from Haight-Ashbury)
    for i in range(n_friends):
        idx = friend_district_indices[i]
        tt = travel_time[0][idx]
        s.add(Implies(And(meet[i], position[i] == 0), start[i] >= 540 + tt))  # 540 = 9:00 AM in minutes
    
    # Travel constraints between consecutive meetings
    for i in range(n_friends):
        for j in range(n_friends):
            if i == j:
                continue
            idx_i = friend_district_indices[i]
            idx_j = friend_district_indices[j]
            tt = travel_time[idx_i][idx_j]
            s.add(Implies(And(meet[i], meet[j], position[j] == position[i] + 1),
                          end[i] + tt <= start[j]))
    
    # Maximize the number of meetings
    obj = Sum([If(meet[i], 1, 0) for i in range(n_friends)])
    opt = Optimize()
    opt.add(s.assertions())
    opt.maximize(obj)
    
    # Check and get the model
    if opt.check() == sat:
        model = opt.model()
        meetings = []
        for i in range(n_friends):
            if is_true(model.eval(meet[i])):
                pos_val = model.eval(position[i]).as_long()
                start_val = model.eval(start[i]).as_long()
                end_val = model.eval(end[i]).as_long()
                name = friends[i][0]
                meetings.append((pos_val, name, start_val, end_val))
        
        # Sort by position
        meetings.sort(key=lambda x: x[0])
        itinerary = []
        for pos, name, start_min, end_min in meetings:
            start_h = start_min // 60
            start_m = start_min % 60
            end_h = end_min // 60
            end_m = end_min % 60
            start_str = f"{start_h:02d}:{start_m:02d}"
            end_str = f"{end_h:02d}:{end_m:02d}"
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()