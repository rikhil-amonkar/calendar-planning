import z3
import json

# Travel times data as a multi-line string
travel_time_data = """
Sunset District to Presidio: 16.
Sunset District to Nob Hill: 27.
Sunset District to Pacific Heights: 21.
Sunset District to Mission District: 25.
Sunset District to Marina District: 21.
Sunset District to North Beach: 28.
Sunset District to Russian Hill: 24.
Sunset District to Richmond District: 12.
Sunset District to Embarcadero: 30.
Sunset District to Alamo Square: 17.
Presidio to Sunset District: 15.
Presidio to Nob Hill: 18.
Presidio to Pacific Heights: 11.
Presidio to Mission District: 26.
Presidio to Marina District: 11.
Presidio to North Beach: 18.
Presidio to Russian Hill: 14.
Presidio to Richmond District: 7.
Presidio to Embarcadero: 20.
Presidio to Alamo Square: 19.
Nob Hill to Sunset District: 24.
Nob Hill to Presidio: 17.
Nob Hill to Pacific Heights: 8.
Nob Hill to Mission District: 13.
Nob Hill to Marina District: 11.
Nob Hill to North Beach: 8.
Nob Hill to Russian Hill: 5.
Nob Hill to Richmond District: 14.
Nob Hill to Embarcadero: 9.
Nob Hill to Alamo Square: 11.
Pacific Heights to Sunset District: 21.
Pacific Heights to Presidio: 11.
Pacific Heights to Nob Hill: 8.
Pacific Heights to Mission District: 15.
Pacific Heights to Marina District: 6.
Pacific Heights to North Beach: 9.
Pacific Heights to Russian Hill: 7.
Pacific Heights to Richmond District: 12.
Pacific Heights to Embarcadero: 10.
Pacific Heights to Alamo Square: 10.
Mission District to Sunset District: 24.
Mission District to Presidio: 25.
Mission District to Nob Hill: 12.
Mission District to Pacific Heights: 16.
Mission District to Marina District: 19.
Mission District to North Beach: 17.
Mission District to Russian Hill: 15.
Mission District to Richmond District: 20.
Mission District to Embarcadero: 19.
Mission District to Alamo Square: 11.
Marina District to Sunset District: 19.
Marina District to Presidio: 10.
Marina District to Nob Hill: 12.
Marina District to Pacific Heights: 7.
Marina District to Mission District: 20.
Marina District to North Beach: 11.
Marina District to Russian Hill: 8.
Marina District to Richmond District: 11.
Marina District to Embarcadero: 14.
Marina District to Alamo Square: 15.
North Beach to Sunset District: 27.
North Beach to Presidio: 17.
North Beach to Nob Hill: 7.
North Beach to Pacific Heights: 8.
North Beach to Mission District: 18.
North Beach to Marina District: 9.
North Beach to Russian Hill: 4.
North Beach to Richmond District: 18.
North Beach to Embarcadero: 6.
North Beach to Alamo Square: 16.
Russian Hill to Sunset District: 23.
Russian Hill to Presidio: 14.
Russian Hill to Nob Hill: 5.
Russian Hill to Pacific Heights: 7.
Russian Hill to Mission District: 16.
Russian Hill to Marina District: 7.
Russian Hill to North Beach: 5.
Russian Hill to Richmond District: 14.
Russian Hill to Embarcadero: 8.
Russian Hill to Alamo Square: 15.
Richmond District to Sunset District: 11.
Richmond District to Presidio: 7.
Richmond District to Nob Hill: 17.
Richmond District to Pacific Heights: 10.
Richmond District to Mission District: 20.
Richmond District to Marina District: 9.
Richmond District to North Beach: 17.
Richmond District to Russian Hill: 13.
Richmond District to Embarcadero: 19.
Richmond District to Alamo Square: 13.
Embarcadero to Sunset District: 30.
Embarcadero to Presidio: 20.
Embarcadero to Nob Hill: 10.
Embarcadero to Pacific Heights: 11.
Embarcadero to Mission District: 20.
Embarcadero to Marina District: 12.
Embarcadero to North Beach: 5.
Embarcadero to Russian Hill: 8.
Embarcadero to Richmond District: 21.
Embarcadero to Alamo Square: 19.
Alamo Square to Sunset District: 16.
Alamo Square to Presidio: 17.
Alamo Square to Nob Hill: 11.
Alamo Square to Pacific Heights: 10.
Alamo Square to Mission District: 10.
Alamo Square to Marina District: 15.
Alamo Square to North Beach: 15.
Alamo Square to Russian Hill: 13.
Alamo Square to Richmond District: 11.
Alamo Square to Embarcadero: 16.
"""

# Parse the travel time data
travel_times = {}
lines = travel_time_data.strip().split('\n')
for line in lines:
    if not line.strip():
        continue
    parts = line.split(':')
    if len(parts) < 2:
        continue
    time_str = parts[1].strip().rstrip('.').strip()
    try:
        time_val = int(time_str)
    except ValueError:
        continue
    from_to_str = parts[0].strip()
    if " to " not in from_to_str:
        continue
    from_loc, to_loc = from_to_str.split(" to ")
    from_loc = from_loc.strip()
    to_loc = to_loc.strip()
    travel_times[(from_loc, to_loc)] = time_val

# Define friends with their details (times in minutes from 9:00 AM)
friends = [
    {'name': 'Charles', 'location': 'Presidio', 'start_available': 255, 'end_available': 360, 'min_duration': 105},
    {'name': 'Robert', 'location': 'Nob Hill', 'start_available': 255, 'end_available': 510, 'min_duration': 90},
    {'name': 'Nancy', 'location': 'Pacific Heights', 'start_available': 345, 'end_available': 780, 'min_duration': 105},
    {'name': 'Brian', 'location': 'Mission District', 'start_available': 390, 'end_available': 780, 'min_duration': 60},
    {'name': 'Kimberly', 'location': 'Marina District', 'start_available': 480, 'end_available': 645, 'min_duration': 75},
    {'name': 'David', 'location': 'North Beach', 'start_available': 345, 'end_available': 450, 'min_duration': 75},
    {'name': 'William', 'location': 'Russian Hill', 'start_available': 210, 'end_available': 615, 'min_duration': 120},
    {'name': 'Jeffrey', 'location': 'Richmond District', 'start_available': 180, 'end_available': 615, 'min_duration': 45},
    {'name': 'Karen', 'location': 'Embarcadero', 'start_available': 315, 'end_available': 705, 'min_duration': 60},
    {'name': 'Joshua', 'location': 'Alamo Square', 'start_available': 585, 'end_available': 780, 'min_duration': 60}
]

# Create Z3 solver
solver = z3.Solver()
opt = z3.Optimize()

# Create variables
meet_vars = {}
s_vars = {}
e_vars = {}
for friend in friends:
    name = friend['name']
    meet_vars[name] = z3.Bool(f"meet_{name}")
    s_vars[name] = z3.Int(f"s_{name}")
    e_vars[name] = s_vars[name] + friend['min_duration']

# Add constraints: availability and travel from Sunset
for friend in friends:
    name = friend['name']
    loc = friend['location']
    start_avail = friend['start_available']
    end_avail = friend['end_available']
    min_dur = friend['min_duration']
    
    # If we meet the friend, then:
    #   start time >= available_start and end time <= available_end
    #   start time >= travel time from Sunset to the friend's location
    opt.add(z3.Implies(meet_vars[name], s_vars[name] >= start_avail))
    opt.add(z3.Implies(meet_vars[name], e_vars[name] <= end_avail))
    travel_key = ('Sunset District', loc)
    if travel_key in travel_times:
        sunset_travel = travel_times[travel_key]
        opt.add(z3.Implies(meet_vars[name], s_vars[name] >= sunset_travel))
    else:
        print(f"Warning: travel time not found from Sunset District to {loc}")

# Add pairwise constraints for every pair of distinct friends
n = len(friends)
for i in range(n):
    for j in range(i+1, n):
        friend_i = friends[i]
        friend_j = friends[j]
        name_i = friend_i['name']
        name_j = friend_j['name']
        loc_i = friend_i['location']
        loc_j = friend_j['location']
        
        # Travel times between the two friends' locations
        travel_key_ij = (loc_i, loc_j)
        travel_key_ji = (loc_j, loc_i)
        
        if travel_key_ij in travel_times and travel_key_ji in travel_times:
            travel_ij = travel_times[travel_key_ij]
            travel_ji = travel_times[travel_key_ji]
            # If both are met, then either i after j or j after i
            constraint = z3.Or(
                s_vars[name_i] >= e_vars[name_j] + travel_ji,
                s_vars[name_j] >= e_vars[name_i] + travel_ij
            )
            opt.add(z3.Implies(z3.And(meet_vars[name_i], meet_vars[name_j]), constraint))
        else:
            print(f"Warning: travel time not found between {loc_i} and {loc_j}")

# Objective: maximize the number of friends met
objective = z3.Sum([z3.If(meet_vars[friend['name']], 1, 0) for friend in friends])
opt.maximize(objective)

# Solve the problem
if opt.check() == z3.sat:
    model = opt.model()
    itinerary = []
    for friend in friends:
        name = friend['name']
        if z3.is_true(model[meet_vars[name]]):
            start_val = model[s_vars[name]].as_long()
            end_val = start_val + friend['min_duration']
            # Convert minutes since 9:00 AM to time string
            total_minutes_start = start_val
            h_start = 9 + total_minutes_start // 60
            m_start = total_minutes_start % 60
            start_time_str = f"{h_start:02d}:{m_start:02d}"
            total_minutes_end = end_val
            h_end = 9 + total_minutes_end // 60
            m_end = total_minutes_end % 60
            end_time_str = f"{h_end:02d}:{m_end:02d}"
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_time_str,
                "end_time": end_time_str
            })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x['start_time'])
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result, indent=2))
else:
    print("No solution found")