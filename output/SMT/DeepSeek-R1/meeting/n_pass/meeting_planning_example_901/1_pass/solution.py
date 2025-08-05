from z3 import *
import json

def main():
    # Define the friends and their data: (name, location, (availability_start, availability_end) in fractional hours, min_time in hours)
    friends = [
        ("Emily", "Pacific Heights", (9.25, 13.75), 120/60),   # 9:15AM to 1:45PM, min 120 min = 2 hours
        ("Helen", "North Beach", (13.75, 18.75), 30/60),        # 1:45PM to 6:45PM, min 30 min
        ("Kimberly", "Golden Gate Park", (18.75, 21.25), 75/60), # 6:45PM to 9:15PM, min 75 min
        ("James", "Embarcadero", (10.5, 11.5), 30/60),          # 10:30AM to 11:30AM, min 30 min
        ("Linda", "Haight-Ashbury", (7.5, 19.25), 15/60),       # 7:30AM to 7:15PM, min 15 min
        ("Paul", "Fisherman's Wharf", (14.75, 18.75), 90/60),   # 2:45PM to 6:45PM, min 90 min
        ("Anthony", "Mission District", (8.0, 14.75), 105/60),  # 8:00AM to 2:45PM, min 105 min
        ("Nancy", "Alamo Square", (8.5, 13.75), 120/60),        # 8:30AM to 1:45PM, min 120 min
        ("William", "Bayview", (17.5, 20.5), 120/60),           # 5:30PM to 8:30PM, min 120 min
        ("Margaret", "Richmond District", (15.25, 18.25), 45/60) # 3:15PM to 6:15PM, min 45 min
    ]
    
    # Build travel time dictionary from the provided text
    travel_text = """
    Russian Hill to Pacific Heights: 7.
    Russian Hill to North Beach: 5.
    Russian Hill to Golden Gate Park: 21.
    Russian Hill to Embarcadero: 8.
    Russian Hill to Haight-Ashbury: 17.
    Russian Hill to Fisherman's Wharf: 7.
    Russian Hill to Mission District: 16.
    Russian Hill to Alamo Square: 15.
    Russian Hill to Bayview: 23.
    Russian Hill to Richmond District: 14.
    Pacific Heights to Russian Hill: 7.
    Pacific Heights to North Beach: 9.
    Pacific Heights to Golden Gate Park: 15.
    Pacific Heights to Embarcadero: 10.
    Pacific Heights to Haight-Ashbury: 11.
    Pacific Heights to Fisherman's Wharf: 13.
    Pacific Heights to Mission District: 15.
    Pacific Heights to Alamo Square: 10.
    Pacific Heights to Bayview: 22.
    Pacific Heights to Richmond District: 12.
    North Beach to Russian Hill: 4.
    North Beach to Pacific Heights: 8.
    North Beach to Golden Gate Park: 22.
    North Beach to Embarcadero: 6.
    North Beach to Haight-Ashbury: 18.
    North Beach to Fisherman's Wharf: 5.
    North Beach to Mission District: 18.
    North Beach to Alamo Square: 16.
    North Beach to Bayview: 25.
    North Beach to Richmond District: 18.
    Golden Gate Park to Russian Hill: 19.
    Golden Gate Park to Pacific Heights: 16.
    Golden Gate Park to North Beach: 23.
    Golden Gate Park to Embarcadero: 25.
    Golden Gate Park to Haight-Ashbury: 7.
    Golden Gate Park to Fisherman's Wharf: 24.
    Golden Gate Park to Mission District: 17.
    Golden Gate Park to Alamo Square: 9.
    Golden Gate Park to Bayview: 23.
    Golden Gate Park to Richmond District: 7.
    Embarcadero to Russian Hill: 8.
    Embarcadero to Pacific Heights: 11.
    Embarcadero to North Beach: 5.
    Embarcadero to Golden Gate Park: 25.
    Embarcadero to Haight-Ashbury: 21.
    Embarcadero to Fisherman's Wharf: 6.
    Embarcadero to Mission District: 20.
    Embarcadero to Alamo Square: 19.
    Embarcadero to Bayview: 21.
    Embarcadero to Richmond District: 21.
    Haight-Ashbury to Russian Hill: 17.
    Haight-Ashbury to Pacific Heights: 12.
    Haight-Ashbury to North Beach: 19.
    Haight-Ashbury to Golden Gate Park: 7.
    Haight-Ashbury to Embarcadero: 20.
    Haight-Ashbury to Fisherman's Wharf: 23.
    Haight-Ashbury to Mission District: 11.
    Haight-Ashbury to Alamo Square: 5.
    Haight-Ashbury to Bayview: 18.
    Haight-Ashbury to Richmond District: 10.
    Fisherman's Wharf to Russian Hill: 7.
    Fisherman's Wharf to Pacific Heights: 12.
    Fisherman's Wharf to North Beach: 6.
    Fisherman's Wharf to Golden Gate Park: 25.
    Fisherman's Wharf to Embarcadero: 8.
    Fisherman's Wharf to Haight-Ashbury: 22.
    Fisherman's Wharf to Mission District: 22.
    Fisherman's Wharf to Alamo Square: 21.
    Fisherman's Wharf to Bayview: 26.
    Fisherman's Wharf to Richmond District: 18.
    Mission District to Russian Hill: 15.
    Mission District to Pacific Heights: 16.
    Mission District to North Beach: 17.
    Mission District to Golden Gate Park: 17.
    Mission District to Embarcadero: 19.
    Mission District to Haight-Ashbury: 12.
    Mission District to Fisherman's Wharf: 22.
    Mission District to Alamo Square: 11.
    Mission District to Bayview: 14.
    Mission District to Richmond District: 20.
    Alamo Square to Russian Hill: 13.
    Alamo Square to Pacific Heights: 10.
    Alamo Square to North Beach: 15.
    Alamo Square to Golden Gate Park: 9.
    Alamo Square to Embarcadero: 16.
    Alamo Square to Haight-Ashbury: 5.
    Alamo Square to Fisherman's Wharf: 19.
    Alamo Square to Mission District: 10.
    Alamo Square to Bayview: 16.
    Alamo Square to Richmond District: 11.
    Bayview to Russian Hill: 23.
    Bayview to Pacific Heights: 23.
    Bayview to North Beach: 22.
    Bayview to Golden Gate Park: 22.
    Bayview to Embarcadero: 19.
    Bayview to Haight-Ashbury: 19.
    Bayview to Fisherman's Wharf: 25.
    Bayview to Mission District: 13.
    Bayview to Alamo Square: 16.
    Bayview to Richmond District: 25.
    Richmond District to Russian Hill: 13.
    Richmond District to Pacific Heights: 10.
    Richmond District to North Beach: 17.
    Richmond District to Golden Gate Park: 9.
    Richmond District to Embarcadero: 19.
    Richmond District to Haight-Ashbury: 10.
    Richmond District to Fisherman's Wharf: 18.
    Richmond District to Mission District: 20.
    Richmond District to Alamo Square: 13.
    Richmond District to Bayview: 27.
    """
    
    travel_dict = {}
    lines = travel_text.strip().split('\n')
    for line in lines:
        parts = line.split(':')
        if len(parts) < 2:
            continue
        time_str = parts[1].strip().rstrip('.').strip()
        try:
            time_val = int(time_str)
        except:
            continue
        locs_str = parts[0].strip()
        if " to " not in locs_str:
            continue
        from_loc, to_loc = locs_str.split(" to ")
        from_loc = from_loc.strip()
        to_loc = to_loc.strip()
        travel_dict[(from_loc, to_loc)] = time_val
    
    # Initialize Z3 solver
    s = Optimize()
    s.set("timeout", 300000)  # 5 minutes timeout
    
    n = len(friends)
    met = [Bool(f'met_{i}') for i in range(n)]
    start = [Real(f'start_{i}') for i in range(n)]
    end = [Real(f'end_{i}') for i in range(n)]
    
    # Add constraints for each friend
    for i in range(n):
        name, loc, (avail_start, avail_end), min_time = friends[i]
        # Constraints if met
        s.add(Implies(met[i], start[i] >= avail_start))
        s.add(Implies(met[i], end[i] <= avail_end))
        s.add(Implies(met[i], end[i] - start[i] >= min_time))
        # Travel time from Russian Hill to friend's location
        travel_time = travel_dict[("Russian Hill", loc)] / 60.0
        s.add(Implies(met[i], start[i] >= 9.0 + travel_time))
    
    # Disjunctive constraints for every pair of distinct friends
    for i in range(n):
        for j in range(i+1, n):
            if i == j:
                continue
            _, loc_i, _, _ = friends[i]
            _, loc_j, _, _ = friends[j]
            time_i_j = travel_dict[(loc_i, loc_j)] / 60.0
            time_j_i = travel_dict[(loc_j, loc_i)] / 60.0
            s.add(Implies(And(met[i], met[j]),
                          Or(start[j] >= end[i] + time_i_j,
                             start[i] >= end[j] + time_j_i)))
    
    # Maximize the number of friends met
    s.maximize(Sum([If(met[i], 1, 0) for i in range(n)]))
    
    # Solve and get model
    res = s.check()
    itinerary = []
    if res == sat or (res == unknown and s.reason_unknown() == 'timeout'):
        m = s.model()
        for i in range(n):
            if is_true(m[met[i]]):
                name = friends[i][0]
                # Get start and end times
                s_val = m[start[i]]
                e_val = m[end[i]]
                # Convert to float
                if isinstance(s_val, RatNumRef):
                    s_float = float(s_val.numerator_as_long()) / float(s_val.denominator_as_long())
                elif isinstance(s_val, IntNumRef):
                    s_float = float(s_val.as_long())
                else:
                    s_float = 0.0
                if isinstance(e_val, RatNumRef):
                    e_float = float(e_val.numerator_as_long()) / float(e_val.denominator_as_long())
                elif isinstance(e_val, IntNumRef):
                    e_float = float(e_val.as_long())
                else:
                    e_float = 0.0
                # Convert to minutes since midnight
                start_minutes = int(round(s_float * 60))
                end_minutes = int(round(e_float * 60))
                # Convert to HH:MM
                start_hour = start_minutes // 60
                start_min = start_minutes % 60
                end_hour = end_minutes // 60
                end_min = end_minutes % 60
                start_str = f"{start_hour:02d}:{start_min:02d}"
                end_str = f"{end_hour:02d}:{end_min:02d}"
                itinerary.append({"action": "meet", "person": name, "start_time": start_str, "end_time": end_str})
        # Sort itinerary by start_time
        itinerary.sort(key=lambda x: x['start_time'])
    else:
        itinerary = []
    
    # Output the solution
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()