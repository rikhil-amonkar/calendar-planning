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
        {"name": "Elizabeth", "loc": 1, "start_avail": 630, "end_avail": 1200, "min_dur": 90},  # 10:30AM=630min, 8:00PM=1200min
        # David: Union Square (index2)
        {"name": "David", "loc": 2, "start_avail": 915, "end_avail": 1140, "min_dur": 45},      # 3:15PM=915min, 7:00PM=1140min
        # Sandra: Pacific Heights (index3)
        {"name": "Sandra", "loc": 3, "start_avail": 420, "end_avail": 1200, "min_dur": 120},    # 7:00AM=420min, 8:00PM=1200min
        # Thomas: Bayview (index4)
        {"name": "Thomas", "loc": 4, "start_avail": 1170, "end_avail": 1230, "min_dur": 30},     # 7:30PM=1170min, 8:30PM=1230min
        # Robert: Fisherman's Wharf (index5)
        {"name": "Robert", "loc": 5, "start_avail": 600, "end_avail": 900, "min_dur": 15},      # 10:00AM=600min, 3:00PM=900min
        # Kenneth: Marina District (index6)
        {"name": "Kenneth", "loc": 6, "start_avail": 645, "end_avail": 780, "min_dur": 45},      # 10:45AM=645min, 1:00PM=780min
        # Melissa: Richmond District (index7)
        {"name": "Melissa", "loc": 7, "start_avail": 1095, "end_avail": 1200, "min_dur": 15},   # 6:15PM=1095min, 8:00PM=1200min
        # Kimberly: Sunset District (index8)
        {"name": "Kimberly", "loc": 8, "start_avail": 615, "end_avail": 1095, "min_dur": 105},  # 10:15AM=615min, 6:15PM=1095min
        # Amanda: Golden Gate Park (index9)
        {"name": "Amanda", "loc": 9, "start_avail": 465, "end_avail": 1125, "min_dur": 15}      # 7:45AM=465min, 6:45PM=1125min
    ]
    
    # Create Z3 solver
    s = Optimize()
    
    # Constants
    time0 = 540  # 9:00 AM in minutes (starting time at Haight-Ashbury)
    
    # Variables for friends (index 1 to 9)
    do = [None] * 10  # 0-9 (0 unused)
    time = [None] * 10
    order = [None] * 10
    
    for i in range(1, 10):
        do[i] = Bool(f'do_{i}')
        time[i] = Int(f'time_{i}')
        order[i] = Int(f'order_{i}')
    
    # Constraints list
    constraints = []
    
    # Individual meeting constraints
    for idx in range(1, 10):
        i = idx
        friend = friends[i-1]
        loc = friend["loc"]
        
        # If meeting occurs, it must be within availability window
        constraints.append(
            Implies(do[i], 
                    And(time[i] >= friend["start_avail"], 
                        time[i] + friend["min_dur"] <= friend["end_avail"]))
        )
        
        # If meeting is first in sequence, must account for travel from start
        constraints.append(
            Implies(And(do[i], order[i] == 1),
                    time[i] >= time0 + travel[0][loc])
        )
        
        # Order must be between 1 and 9 if meeting occurs
        constraints.append(
            Implies(do[i], And(order[i] >= 1, order[i] <= 9))
        )
    
    # Unique order numbers for meetings
    for i in range(1, 10):
        for j in range(i+1, 10):
            constraints.append(
                Implies(And(do[i], do[j]), order[i] != order[j])
            )
    
    # Travel time constraints between consecutive meetings
    for i in range(1, 10):
        for j in range(1, 10):
            if i == j:
                continue
            friend_i = friends[i-1]
            friend_j = friends[j-1]
            loc_i = friend_i["loc"]
            loc_j = friend_j["loc"]
            
            constraints.append(
                Implies(And(do[i], do[j], order[j] == order[i] - 1),
                        time[i] >= time[j] + friend_j["min_dur"] + travel[loc_j][loc_i])
            )
    
    # Predecessor existence constraints
    for i in range(1, 10):
        predecessors = []
        for j in range(1, 10):
            if i == j:
                continue
            predecessors.append(And(do[j], order[j] == order[i] - 1))
        
        constraints.append(
            Implies(And(do[i], order[i] >= 2), Or(predecessors))
        )
    
    # Maximize number of meetings
    s.maximize(Sum([If(do[i], 1, 0) for i in range(1, 10)]))
    s.add(constraints)
    
    # Solve and output
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(1, 10):
            if m.evaluate(do[i]):
                start_min = m.evaluate(time[i]).as_long()
                friend = friends[i-1]
                end_min = start_min + friend["min_dur"]
                
                # Convert to HH:MM format
                start_time = f"{start_min//60:02d}:{start_min%60:02d}"
                end_time = f"{end_min//60:02d}:{end_min%60:02d}"
                
                itinerary.append({
                    "action": "meet",
                    "person": friend["name"],
                    "start_time": start_time,
                    "end_time": end_time
                })
        
        # Sort by start time
        itinerary.sort(key=lambda x: x["start_time"])
        print('SOLUTION:')
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print("No solution found")

if __name__ == "__main__":
    main()