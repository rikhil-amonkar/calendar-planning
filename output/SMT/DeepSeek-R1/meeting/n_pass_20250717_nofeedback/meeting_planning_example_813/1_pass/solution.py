from z3 import *
import json

def main():
    # Define the meetings data for real meetings (index 0 to 7)
    meetings = [
        # (name, location, available_start, available_end, duration)
        ("Joshua", "Embarcadero", 9*60+45, 18*60, 105),
        ("Jeffrey", "Bayview", 9*60+45, 20*60+15, 75),
        ("Charles", "Union Square", 10*60+45, 20*60+15, 120),
        ("Joseph", "Chinatown", 7*60, 15*60+30, 60),
        ("Matthew", "Golden Gate Park", 11*60, 19*60+30, 45),
        ("Carol", "Financial District", 10*60+45, 11*60+15, 15),
        ("Paul", "Haight-Ashbury", 19*60+15, 20*60+30, 15),
        ("Rebecca", "Mission District", 17*60, 21*60+45, 45)
    ]
    
    # Dummy meeting at Marina District at 9:00 AM
    dummy_location = "Marina District"
    dummy_start = 9 * 60  # 9:00 AM in minutes
    dummy_end = 9 * 60
    
    # Travel time data as a multi-line string
    travel_data = """
Marina District to Embarcadero: 14.
Marina District to Bayview: 27.
Marina District to Union Square: 16.
Marina District to Chinatown: 15.
Marina District to Sunset District: 19.
Marina District to Golden Gate Park: 18.
Marina District to Financial District: 17.
Marina District to Haight-Ashbury: 16.
Marina District to Mission District: 20.
Embarcadero to Marina District: 12.
Embarcadero to Bayview: 21.
Embarcadero to Union Square: 10.
Embarcadero to Chinatown: 7.
Embarcadero to Sunset District: 30.
Embarcadero to Golden Gate Park: 25.
Embarcadero to Financial District: 5.
Embarcadero to Haight-Ashbury: 21.
Embarcadero to Mission District: 20.
Bayview to Marina District: 27.
Bayview to Embarcadero: 19.
Bayview to Union Square: 18.
Bayview to Chinatown: 19.
Bayview to Sunset District: 23.
Bayview to Golden Gate Park: 22.
Bayview to Financial District: 19.
Bayview to Haight-Ashbury: 19.
Bayview to Mission District: 13.
Union Square to Marina District: 18.
Union Square to Embarcadero: 11.
Union Square to Bayview: 15.
Union Square to Chinatown: 7.
Union Square to Sunset District: 27.
Union Square to Golden Gate Park: 22.
Union Square to Financial District: 9.
Union Square to Haight-Ashbury: 18.
Union Square to Mission District: 14.
Chinatown to Marina District: 12.
Chinatown to Embarcadero: 5.
Chinatown to Bayview: 20.
Chinatown to Union Square: 7.
Chinatown to Sunset District: 29.
Chinatown to Golden Gate Park: 23.
Chinatown to Financial District: 5.
Chinatown to Haight-Ashbury: 19.
Chinatown to Mission District: 17.
Sunset District to Marina District: 21.
Sunset District to Embarcadero: 30.
Sunset District to Bayview: 22.
Sunset District to Union Square: 30.
Sunset District to Chinatown: 30.
Sunset District to Golden Gate Park: 11.
Sunset District to Financial District: 30.
Sunset District to Haight-Ashbury: 15.
Sunset District to Mission District: 25.
Golden Gate Park to Marina District: 16.
Golden Gate Park to Embarcadero: 25.
Golden Gate Park to Bayview: 23.
Golden Gate Park to Union Square: 22.
Golden Gate Park to Chinatown: 23.
Golden Gate Park to Sunset District: 10.
Golden Gate Park to Financial District: 26.
Golden Gate Park to Haight-Ashbury: 7.
Golden Gate Park to Mission District: 17.
Financial District to Marina District: 15.
Financial District to Embarcadero: 4.
Financial District to Bayview: 19.
Financial District to Union Square: 9.
Financial District to Chinatown: 5.
Financial District to Sunset District: 30.
Financial District to Golden Gate Park: 23.
Financial District to Haight-Ashbury: 19.
Financial District to Mission District: 17.
Haight-Ashbury to Marina District: 17.
Haight-Ashbury to Embarcadero: 20.
Haight-Ashbury to Bayview: 18.
Haight-Ashbury to Union Square: 19.
Haight-Ashbury to Chinatown: 19.
Haight-Ashbury to Sunset District: 15.
Haight-Ashbury to Golden Gate Park: 7.
Haight-Ashbury to Financial District: 21.
Haight-Ashbury to Mission District: 11.
Mission District to Marina District: 19.
Mission District to Embarcadero: 19.
Mission District to Bayview: 14.
Mission District to Union Square: 15.
Mission District to Chinatown: 16.
Mission District to Sunset District: 24.
Mission District to Golden Gate Park: 17.
Mission District to Financial District: 15.
Mission District to Haight-Ashbury: 12.
    """
    
    # Parse the travel data
    travel_dict = {}
    lines = travel_data.strip().split('\n')
    for line in lines:
        line = line.strip()
        if line.endswith('.'):
            line = line[:-1]  # remove the trailing dot
        parts = line.split(':')
        if len(parts) < 2:
            continue
        time_val = int(parts[1].strip())
        loc_str = parts[0].strip()
        if " to " in loc_str:
            from_loc, to_loc = loc_str.split(" to ")
            from_loc = from_loc.strip()
            to_loc = to_loc.strip()
            travel_dict[(from_loc, to_loc)] = time_val

    # Our set of locations (8 real + dummy)
    our_locations = set([
        "Marina District", 
        "Embarcadero", "Bayview", "Union Square", "Chinatown", 
        "Golden Gate Park", "Financial District", "Haight-Ashbury", "Mission District"
    ])
    
    # Build a clean travel_dict that only includes our_locations
    travel_dict_clean = {}
    for (from_loc, to_loc), time_val in travel_dict.items():
        if from_loc in our_locations and to_loc in our_locations:
            travel_dict_clean[(from_loc, to_loc)] = time_val

    # Locations for our meetings (real and dummy)
    #   index 0..7: real meetings, index 8: dummy
    locations = [ meeting[1] for meeting in meetings ] + [dummy_location]
    
    # Create the solver
    solver = Optimize()
    
    # Variables for real meetings (0..7)
    m = [ Bool(f'm_{i}') for i in range(8) ]
    s = [ Int(f's_{i}') for i in range(8) ]
    e = [ Int(f'e_{i}') for i in range(8) ]
    
    # Dummy meeting (index 8) - we treat it separately
    s8 = Int('s8')
    e8 = Int('e8')
    solver.add(s8 == dummy_start, e8 == dummy_start)
    
    # Combine all s and e for the disjunctive constraints (for indices 0..8)
    s_all = s + [s8]
    e_all = e + [e8]
    
    # Constraints for real meetings
    for i in range(8):
        name, loc, available_start, available_end, duration = meetings[i]
        solver.add(Implies(m[i], 
            And(
                s[i] >= available_start,
                e[i] == s[i] + duration,
                e[i] <= available_end
            )
        ))
    
    # Disjunctive constraints for every pair of meetings (including dummy) i != j
    for i in range(9):
        for j in range(9):
            if i == j:
                continue
            # Active condition: for real meetings, use the boolean m; for dummy (index 8), it's always active.
            active_i = m[i] if i < 8 else BoolVal(True)
            active_j = m[j] if j < 8 else BoolVal(True)
            active = And(active_i, active_j)
            
            # Get travel times
            from_loc_i = locations[i]
            to_loc_j = locations[j]
            time_ij = travel_dict_clean.get((from_loc_i, to_loc_j))
            if time_ij is None:
                # It should not happen, but if does, skip
                continue
                
            from_loc_j = locations[j]
            to_loc_i = locations[i]
            time_ji = travel_dict_clean.get((from_loc_j, to_loc_i))
            if time_ji is None:
                continue
                
            # Add the disjunctive constraint
            solver.add(Implies(active, 
                Or( 
                    s_all[j] >= e_all[i] + time_ij,
                    s_all[i] >= e_all[j] + time_ji
                )))
    
    # Maximize the number of meetings
    objective = Sum([If(m_i, 1, 0) for m_i in m])
    solver.maximize(objective)
    
    # Check the solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(8):
            if model.eval(m[i]):
                name = meetings[i][0]
                start_min = model.eval(s[i]).as_long()
                end_min = model.eval(e[i]).as_long()
                start_hour = start_min // 60
                start_minute = start_min % 60
                end_hour = end_min // 60
                end_minute = end_min % 60
                start_time = f"{start_hour:02d}:{start_minute:02d}"
                end_time = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Sort by start_time
        itinerary.sort(key=lambda x: x['start_time'])
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()