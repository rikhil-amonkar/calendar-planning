from z3 import *
import json

# Define travel times between locations
sources = [
    "The Castro",
    "Alamo Square",
    "Richmond District",
    "Financial District",
    "Union Square",
    "Fisherman's Wharf",
    "Marina District",
    "Haight-Ashbury",
    "Mission District",
    "Pacific Heights",
    "Golden Gate Park"
]

dest_lists = [
    [("Alamo Square", 8), ("Richmond District", 16), ("Financial District", 21), ("Union Square", 19), ("Fisherman's Wharf", 24), ("Marina District", 21), ("Haight-Ashbury", 6), ("Mission District", 7), ("Pacific Heights", 16), ("Golden Gate Park", 11)],
    [("The Castro", 8), ("Richmond District", 11), ("Financial District", 17), ("Union Square", 14), ("Fisherman's Wharf", 19), ("Marina District", 15), ("Haight-Ashbury", 5), ("Mission District", 10), ("Pacific Heights", 10), ("Golden Gate Park", 9)],
    [("The Castro", 16), ("Alamo Square", 13), ("Financial District", 22), ("Union Square", 21), ("Fisherman's Wharf", 18), ("Marina District", 9), ("Haight-Ashbury", 10), ("Mission District", 20), ("Pacific Heights", 10), ("Golden Gate Park", 9)],
    [("The Castro", 20), ("Alamo Square", 17), ("Richmond District", 21), ("Union Square", 9), ("Fisherman's Wharf", 10), ("Marina District", 15), ("Haight-Ashbury", 19), ("Mission District", 17), ("Pacific Heights", 13), ("Golden Gate Park", 23)],
    [("The Castro", 17), ("Alamo Square", 15), ("Richmond District", 20), ("Financial District", 9), ("Fisherman's Wharf", 15), ("Marina District", 18), ("Haight-Ashbury", 18), ("Mission District", 14), ("Pacific Heights", 15), ("Golden Gate Park", 22)],
    [("The Castro", 27), ("Alamo Square", 21), ("Richmond District", 18), ("Financial District", 11), ("Union Square", 13), ("Marina District", 9), ("Haight-Ashbury", 22), ("Mission District", 22), ("Pacific Heights", 12), ("Golden Gate Park", 25)],
    [("The Castro", 22), ("Alamo Square", 15), ("Richmond District", 11), ("Financial District", 17), ("Union Square", 16), ("Fisherman's Wharf", 10), ("Haight-Ashbury", 16), ("Mission District", 20), ("Pacific Heights", 7), ("Golden Gate Park", 18)],
    [("The Castro", 6), ("Alamo Square", 5), ("Richmond District", 10), ("Financial District", 21), ("Union Square", 19), ("Fisherman's Wharf", 23), ("Marina District", 17), ("Mission District", 11), ("Pacific Heights", 12), ("Golden Gate Park", 7)],
    [("The Castro", 7), ("Alamo Square", 11), ("Richmond District", 20), ("Financial District", 15), ("Union Square", 15), ("Fisherman's Wharf", 22), ("Marina District", 19), ("Haight-Ashbury", 12), ("Pacific Heights", 16), ("Golden Gate Park", 17)],
    [("The Castro", 16), ("Alamo Square", 10), ("Richmond District", 12), ("Financial District", 13), ("Union Square", 12), ("Fisherman's Wharf", 13), ("Marina District", 6), ("Haight-Ashbury", 11), ("Mission District", 15), ("Golden Gate Park", 15)],
    [("The Castro", 13), ("Alamo Square", 9), ("Richmond District", 7), ("Financial District", 26), ("Union Square", 22), ("Fisherman's Wharf", 24), ("Marina District", 16), ("Haight-Ashbury", 7), ("Mission District", 17), ("Pacific Heights", 16)]
]

travel_time = {}
for idx in range(len(sources)):
    source = sources[idx]
    for (dest, t) in dest_lists[idx]:
        travel_time[(source, dest)] = t

# Define friends with their details in minutes
friends = [
    {"name": "William", "location": "Alamo Square", "start_avail": 15*60+15, "end_avail": 17*60+15, "min_time": 60},
    {"name": "Joshua", "location": "Richmond District", "start_avail": 7*60, "end_avail": 20*60, "min_time": 15},
    {"name": "Joseph", "location": "Financial District", "start_avail": 11*60+15, "end_avail": 13*60+30, "min_time": 15},
    {"name": "David", "location": "Union Square", "start_avail": 16*60+45, "end_avail": 19*60+15, "min_time": 45},
    {"name": "Brian", "location": "Fisherman's Wharf", "start_avail": 13*60+45, "end_avail": 20*60+45, "min_time": 105},
    {"name": "Karen", "location": "Marina District", "start_avail": 11*60+30, "end_avail": 18*60+30, "min_time": 15},
    {"name": "Anthony", "location": "Haight-Ashbury", "start_avail": 7*60+15, "end_avail": 10*60+30, "min_time": 30},
    {"name": "Matthew", "location": "Mission District", "start_avail": 17*60+15, "end_avail": 19*60+15, "min_time": 120},
    {"name": "Helen", "location": "Pacific Heights", "start_avail": 8*60, "end_avail": 12*60, "min_time": 75},
    {"name": "Jeffrey", "location": "Golden Gate Park", "start_avail": 19*60, "end_avail": 21*60+30, "min_time": 60}
]

# Initialize Z3 solver and variables
s = Optimize()
meet_vars = []
start_vars = []
end_vars = []
friend_locations = []

for i, friend in enumerate(friends):
    name = friend["name"]
    meet_vars.append(Bool(f"meet_{name}"))
    start_vars.append(Int(f"start_{name}"))
    end_vars.append(Int(f"end_{name}"))
    friend_locations.append(friend["location"])

# Add constraints for each friend
for i, friend in enumerate(friends):
    s.add(Implies(meet_vars[i], start_vars[i] >= 540 + travel_time[("The Castro", friend["location"])]))
    s.add(Implies(meet_vars[i], start_vars[i] >= friend["start_avail"]))
    s.add(Implies(meet_vars[i], end_vars[i] == start_vars[i] + friend["min_time"]))
    s.add(Implies(meet_vars[i], end_vars[i] <= friend["end_avail"]))

# Add disjunctive constraints for each pair of friends
for i in range(len(friends)):
    for j in range(i+1, len(friends)):
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        t_ij = travel_time.get((loc_i, loc_j), 0)
        t_ji = travel_time.get((loc_j, loc_i), 0)
        constraint = Or(
            start_vars[i] >= end_vars[j] + t_ji,
            start_vars[j] >= end_vars[i] + t_ij
        )
        s.add(Implies(And(meet_vars[i], meet_vars[j]), constraint))

# Maximize the number of friends met
s.maximize(Sum([If(meet_var, 1, 0) for meet_var in meet_vars]))

# Solve and get the model
if s.check() == sat:
    m = s.model()
    scheduled_meetings = []
    for i, friend in enumerate(friends):
        if m.evaluate(meet_vars[i]):
            start_val = m.evaluate(start_vars[i])
            end_val = m.evaluate(end_vars[i])
            if isinstance(start_val, IntNumRef) and isinstance(end_val, IntNumRef):
                start_min = start_val.as_long()
                end_min = end_val.as_long()
                start_hour = start_min // 60
                start_minute = start_min % 60
                end_hour = end_min // 60
                end_minute = end_min % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                scheduled_meetings.append({
                    "person": friend["name"],
                    "start": start_min,
                    "start_str": start_str,
                    "end_str": end_str
                })
    scheduled_meetings.sort(key=lambda x: x["start"])
    itinerary = [{"action": "meet", "person": mtg["person"], "start_time": mtg["start_str"], "end_time": mtg["end_str"]} for mtg in scheduled_meetings]
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result, indent=2))
else:
    print("No solution found")