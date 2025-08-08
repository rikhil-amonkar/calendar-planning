from z3 import *
import json

# Convert time to minutes from midnight
def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

# Build travel_times dictionary from the provided text
travel_text = """
Embarcadero to Bayview: 21.
Embarcadero to Chinatown: 7.
Embarcadero to Alamo Square: 19.
Embarcadero to Nob Hill: 10.
Embarcadero to Presidio: 20.
Embarcadero to Union Square: 10.
Embarcadero to The Castro: 25.
Embarcadero to North Beach: 5.
Embarcadero to Fisherman's Wharf: 6.
Embarcadero to Marina District: 12.
Bayview to Embarcadero: 19.
Bayview to Chinatown: 19.
Bayview to Alamo Square: 16.
Bayview to Nob Hill: 20.
Bayview to Presidio: 32.
Bayview to Union Square: 18.
Bayview to The Castro: 19.
Bayview to North Beach: 22.
Bayview to Fisherman's Wharf: 25.
Bayview to Marina District: 27.
Chinatown to Embarcadero: 5.
Chinatown to Bayview: 20.
Chinatown to Alamo Square: 17.
Chinatown to Nob Hill: 9.
Chinatown to Presidio: 19.
Chinatown to Union Square: 7.
Chinatown to The Castro: 22.
Chinatown to North Beach: 3.
Chinatown to Fisherman's Wharf: 8.
Chinatown to Marina District: 12.
Alamo Square to Embarcadero: 16.
Alamo Square to Bayview: 16.
Alamo Square to Chinatown: 15.
Alamo Square to Nob Hill: 11.
Alamo Square to Presidio: 17.
Alamo Square to Union Square: 14.
Alamo Square to The Castro: 8.
Alamo Square to North Beach: 15.
Alamo Square to Fisherman's Wharf: 19.
Alamo Square to Marina District: 15.
Nob Hill to Embarcadero: 9.
Nob Hill to Bayview: 19.
Nob Hill to Chinatown: 6.
Nob Hill to Alamo Square: 11.
Nob Hill to Presidio: 17.
Nob Hill to Union Square: 7.
Nob Hill to The Castro: 17.
Nob Hill to North Beach: 8.
Nob Hill to Fisherman's Wharf: 10.
Nob Hill to Marina District: 11.
Presidio to Embarcadero: 20.
Presidio to Bayview: 31.
Presidio to Chinatown: 21.
Presidio to Alamo Square: 19.
Presidio to Nob Hill: 18.
Presidio to Union Square: 22.
Presidio to The Castro: 21.
Presidio to North Beach: 18.
Presidio to Fisherman's Wharf: 19.
Presidio to Marina District: 11.
Union Square to Embarcadero: 11.
Union Square to Bayview: 15.
Union Square to Chinatown: 7.
Union Square to Alamo Square: 15.
Union Square to Nob Hill: 9.
Union Square to Presidio: 24.
Union Square to The Castro: 17.
Union Square to North Beach: 10.
Union Square to Fisherman's Wharf: 15.
Union Square to Marina District: 18.
The Castro to Embarcadero: 22.
The Castro to Bayview: 19.
The Castro to Chinatown: 22.
The Castro to Alamo Square: 8.
The Castro to Nob Hill: 16.
The Castro to Presidio: 20.
The Castro to Union Square: 19.
The Castro to North Beach: 20.
The Castro to Fisherman's Wharf: 24.
The Castro to Marina District: 21.
North Beach to Embarcadero: 6.
North Beach to Bayview: 25.
North Beach to Chinatown: 6.
North Beach to Alamo Square: 16.
North Beach to Nob Hill: 7.
North Beach to Presidio: 17.
North Beach to Union Square: 7.
North Beach to The Castro: 23.
North Beach to Fisherman's Wharf: 5.
North Beach to Marina District: 9.
Fisherman's Wharf to Embarcadero: 8.
Fisherman's Wharf to Bayview: 26.
Fisherman's Wharf to Chinatown: 12.
Fisherman's Wharf to Alamo Square: 21.
Fisherman's Wharf to Nob Hill: 11.
Fisherman's Wharf to Presidio: 17.
Fisherman's Wharf to Union Square: 13.
Fisherman's Wharf to The Castro: 27.
Fisherman's Wharf to North Beach: 6.
Fisherman's Wharf to Marina District: 9.
Marina District to Embarcadero: 14.
Marina District to Bayview: 27.
Marina District to Chinatown: 15.
Marina District to Alamo Square: 15.
Marina District to Nob Hill: 12.
Marina District to Presidio: 10.
Marina District to Union Square: 16.
Marina District to The Castro: 22.
Marina District to North Beach: 11.
Marina District to Fisherman's Wharf: 10.
"""

travel_times = {}
lines = travel_text.strip().split('\n')
for line in lines:
    if not line.strip():
        continue
    parts = line.split(':')
    time_str = parts[1].strip().rstrip('.')
    time_val = int(time_str)
    loc_str = parts[0].strip()
    loc_parts = loc_str.split(' to ')
    from_loc = loc_parts[0].strip()
    to_loc = loc_parts[1].strip()
    travel_times[(from_loc, to_loc)] = time_val

# Define friends and their constraints
friends = [
    ("Matthew", "Bayview", time_to_minutes("19:15"), time_to_minutes("22:00"), 120),
    ("Karen", "Chinatown", time_to_minutes("19:15"), time_to_minutes("21:15"), 90),
    ("Sarah", "Alamo Square", time_to_minutes("20:00"), time_to_minutes("21:45"), 105),
    ("Jessica", "Nob Hill", time_to_minutes("16:30"), time_to_minutes("18:45"), 120),
    ("Stephanie", "Presidio", time_to_minutes("07:30"), time_to_minutes("10:15"), 60),
    ("Mary", "Union Square", time_to_minutes("16:45"), time_to_minutes("21:30"), 60),
    ("Charles", "The Castro", time_to_minutes("16:30"), time_to_minutes("22:00"), 105),
    ("Nancy", "North Beach", time_to_minutes("14:45"), time_to_minutes("20:00"), 15),
    ("Thomas", "Fisherman's Wharf", time_to_minutes("13:30"), time_to_minutes("19:00"), 30),
    ("Brian", "Marina District", time_to_minutes("12:15"), time_to_minutes("18:00"), 60)
]

# Start time at Embarcadero
start_time = time_to_minutes("09:00")  # 540 minutes

# Create Z3 solver and variables
s = Solver()
opt = Optimize()

meet_vars = {}
start_vars = {}
end_vars = {}
for (name, loc, avail_start, avail_end, min_time) in friends:
    meet_vars[name] = Bool(f"meet_{name}")
    start_vars[name] = Int(f"start_{name}")
    end_vars[name] = Int(f"end_{name}")

# Constraints for each friend
for (name, loc, avail_start, avail_end, min_time) in friends:
    opt.add(Implies(meet_vars[name], start_vars[name] >= avail_start))
    opt.add(Implies(meet_vars[name], end_vars[name] <= avail_end))
    opt.add(Implies(meet_vars[name], end_vars[name] - start_vars[name] >= min_time))
    # Travel time from Embarcadero to friend's location
    travel_from_start = travel_times[("Embarcadero", loc)]
    opt.add(Implies(meet_vars[name], start_vars[name] >= start_time + travel_from_start))

# Constraints for every pair of friends
for i in range(len(friends)):
    name_i = friends[i][0]
    loc_i = friends[i][1]
    for j in range(i+1, len(friends)):
        name_j = friends[j][0]
        loc_j = friends[j][1]
        time_ij = travel_times.get((loc_i, loc_j), None)
        time_ji = travel_times.get((loc_j, loc_i), None)
        if time_ij is None or time_ji is None:
            continue
        opt.add(Implies(And(meet_vars[name_i], meet_vars[name_j]),
                         Or(end_vars[name_i] + time_ij <= start_vars[name_j],
                            end_vars[name_j] + time_ji <= start_vars[name_i])))

# Objective: maximize the number of friends met
objective = Sum([If(meet_vars[name], 1, 0) for (name, _, _, _, _) in friends])
opt.maximize(objective)

# Solve and get the model
if opt.check() == sat:
    m = opt.model()
    itinerary = []
    for (name, loc, avail_start, avail_end, min_time) in friends:
        if is_true(m.evaluate(meet_vars[name])):
            start_val = m.evaluate(start_vars[name])
            end_val = m.evaluate(end_vars[name])
            if isinstance(start_val, IntNumRef):
                start_minutes = start_val.as_long()
            else:
                start_minutes = int(str(start_val))
            if isinstance(end_val, IntNumRef):
                end_minutes = end_val.as_long()
            else:
                end_minutes = int(str(end_val))
            start_hour = start_minutes // 60
            start_minute = start_minutes % 60
            end_hour = end_minutes // 60
            end_minute = end_minutes % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })
    # Sort itinerary by start_time using helper function
    itinerary.sort(key=lambda x: time_to_minutes(x['start_time']))
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result, indent=2))
else:
    print("SOLUTION:")
    print('{"itinerary": []}')