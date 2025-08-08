from z3 import *
import re

def to_minutes(time_str):
    time_str = time_str.strip()
    if time_str.endswith('AM') or time_str.endswith('PM'):
        suffix = time_str[-2:]
        time_part = time_str[:-2].strip()
        if ':' in time_part:
            parts = time_part.split(':')
            hour = int(parts[0])
            minute = int(parts[1]) if len(parts) > 1 else 0
        else:
            hour = int(time_part)
            minute = 0
        if suffix == 'PM' and hour != 12:
            hour += 12
        if suffix == 'AM' and hour == 12:
            hour = 0
        return hour * 60 + minute
    else:
        raise ValueError(f"Unknown time format: {time_str}")

friends_data = [
    ("Matthew", "Bayview", "7:15PM", "10:00PM", 120),
    ("Karen", "Chinatown", "7:15PM", "9:15PM", 90),
    ("Sarah", "Alamo Square", "8:00PM", "9:45PM", 105),
    ("Jessica", "Nob Hill", "4:30PM", "6:45PM", 120),
    ("Stephanie", "Presidio", "7:30AM", "10:15AM", 60),
    ("Mary", "Union Square", "4:45PM", "9:30PM", 60),
    ("Charles", "The Castro", "4:30PM", "10:00PM", 105),
    ("Nancy", "North Beach", "2:45PM", "8:00PM", 15),
    ("Thomas", "Fisherman's Wharf", "1:30PM", "7:00PM", 30),
    ("Brian", "Marina District", "12:15PM", "6:00PM", 60)
]

friends = []
for data in friends_data:
    name, loc, start_str, end_str, dur = data
    start_min = to_minutes(start_str)
    end_min = to_minutes(end_str)
    friends.append((name, loc, start_min, end_min, dur))

travel_times_list = [
    ("Embarcadero", "Bayview", 21),
    ("Embarcadero", "Chinatown", 7),
    ("Embarcadero", "Alamo Square", 19),
    ("Embarcadero", "Nob Hill", 10),
    ("Embarcadero", "Presidio", 20),
    ("Embarcadero", "Union Square", 10),
    ("Embarcadero", "The Castro", 25),
    ("Embarcadero", "North Beach", 5),
    ("Embarcadero", "Fisherman's Wharf", 6),
    ("Embarcadero", "Marina District", 12),
    ("Bayview", "Embarcadero", 19),
    ("Bayview", "Chinatown", 19),
    ("Bayview", "Alamo Square", 16),
    ("Bayview", "Nob Hill", 20),
    ("Bayview", "Presidio", 32),
    ("Bayview", "Union Square", 18),
    ("Bayview", "The Castro", 19),
    ("Bayview", "North Beach", 22),
    ("Bayview", "Fisherman's Wharf", 25),
    ("Bayview", "Marina District", 27),
    ("Chinatown", "Embarcadero", 5),
    ("Chinatown", "Bayview", 20),
    ("Chinatown", "Alamo Square", 17),
    ("Chinatown", "Nob Hill", 9),
    ("Chinatown", "Presidio", 19),
    ("Chinatown", "Union Square", 7),
    ("Chinatown", "The Castro", 22),
    ("Chinatown", "North Beach", 3),
    ("Chinatown", "Fisherman's Wharf", 8),
    ("Chinatown", "Marina District", 12),
    ("Alamo Square", "Embarcadero", 16),
    ("Alamo Square", "Bayview", 16),
    ("Alamo Square", "Chinatown", 15),
    ("Alamo Square", "Nob Hill", 11),
    ("Alamo Square", "Presidio", 17),
    ("Alamo Square", "Union Square", 14),
    ("Alamo Square", "The Castro", 8),
    ("Alamo Square", "North Beach", 15),
    ("Alamo Square", "Fisherman's Wharf", 19),
    ("Alamo Square", "Marina District", 15),
    ("Nob Hill", "Embarcadero", 9),
    ("Nob Hill", "Bayview", 19),
    ("Nob Hill", "Chinatown", 6),
    ("Nob Hill", "Alamo Square", 11),
    ("Nob Hill", "Presidio", 17),
    ("Nob Hill", "Union Square", 7),
    ("Nob Hill", "The Castro", 17),
    ("Nob Hill", "North Beach", 8),
    ("Nob Hill", "Fisherman's Wharf", 10),
    ("Nob Hill", "Marina District", 11),
    ("Presidio", "Embarcadero", 20),
    ("Presidio", "Bayview", 31),
    ("Presidio", "Chinatown", 21),
    ("Presidio", "Alamo Square", 19),
    ("Presidio", "Nob Hill", 18),
    ("Presidio", "Union Square", 22),
    ("Presidio", "The Castro", 21),
    ("Presidio", "North Beach", 18),
    ("Presidio", "Fisherman's Wharf", 19),
    ("Presidio", "Marina District", 11),
    ("Union Square", "Embarcadero", 11),
    ("Union Square", "Bayview", 15),
    ("Union Square", "Chinatown", 7),
    ("Union Square", "Alamo Square", 15),
    ("Union Square", "Nob Hill", 9),
    ("Union Square", "Presidio", 24),
    ("Union Square", "The Castro", 17),
    ("Union Square", "North Beach", 10),
    ("Union Square", "Fisherman's Wharf", 15),
    ("Union Square", "Marina District", 18),
    ("The Castro", "Embarcadero", 22),
    ("The Castro", "Bayview", 19),
    ("The Castro", "Chinatown", 22),
    ("The Castro", "Alamo Square", 8),
    ("The Castro", "Nob Hill", 16),
    ("The Castro", "Presidio", 20),
    ("The Castro", "Union Square", 19),
    ("The Castro", "North Beach", 20),
    ("The Castro", "Fisherman's Wharf", 24),
    ("The Castro", "Marina District", 21),
    ("North Beach", "Embarcadero", 6),
    ("North Beach", "Bayview", 25),
    ("North Beach", "Chinatown", 6),
    ("North Beach", "Alamo Square", 16),
    ("North Beach", "Nob Hill", 7),
    ("North Beach", "Presidio", 17),
    ("North Beach", "Union Square", 7),
    ("North Beach", "The Castro", 23),
    ("North Beach", "Fisherman's Wharf", 5),
    ("North Beach", "Marina District", 9),
    ("Fisherman's Wharf", "Embarcadero", 8),
    ("Fisherman's Wharf", "Bayview", 26),
    ("Fisherman's Wharf", "Chinatown", 12),
    ("Fisherman's Wharf", "Alamo Square", 21),
    ("Fisherman's Wharf", "Nob Hill", 11),
    ("Fisherman's Wharf", "Presidio", 17),
    ("Fisherman's Wharf", "Union Square", 13),
    ("Fisherman's Wharf", "The Castro", 27),
    ("Fisherman's Wharf", "North Beach", 6),
    ("Fisherman's Wharf", "Marina District", 9),
    ("Marina District", "Embarcadero", 14),
    ("Marina District", "Bayview", 27),
    ("Marina District", "Chinatown", 15),
    ("Marina District", "Alamo Square", 15),
    ("Marina District", "Nob Hill", 12),
    ("Marina District", "Presidio", 10),
    ("Marina District", "Union Square", 16),
    ("Marina District", "The Castro", 22),
    ("Marina District", "North Beach", 11),
    ("Marina District", "Fisherman's Wharf", 10)
]

travel_dict = {}
for (src, dst, time) in travel_times_list:
    travel_dict[(src, dst)] = time

n = len(friends)
s = [Int(f's_{i}') for i in range(n)]
e = [Int(f'e_{i}') for i in range(n)]
met = [Bool(f'met_{i}') for i in range(n)]

s0 = 540
loc0 = "Embarcadero"

solver = Solver()

for i, (name, loc, start_avail, end_avail, min_dur) in enumerate(friends):
    solver.add(Implies(met[i], s[i] >= start_avail))
    solver.add(Implies(met[i], e[i] <= end_avail))
    solver.add(Implies(met[i], e[i] >= s[i] + min_dur))
    solver.add(Implies(met[i], s[i] >= s0 + travel_dict[(loc0, loc)]))

for i in range(n):
    for j in range(n):
        if i == j:
            continue
        loc_i = friends[i][1]
        loc_j = friends[j][1]
        time_ij = travel_dict.get((loc_i, loc_j), None)
        time_ji = travel_dict.get((loc_j, loc_i), None)
        if time_ij is None or time_ji is None:
            continue
        cond = Or(
            e[i] + time_ij <= s[j],
            e[j] + time_ji <= s[i]
        )
        solver.add(Implies(And(met[i], met[j]), cond))

num_met = Sum([If(met[i], 1, 0) for i in range(n)])

opt = Optimize()
opt.add(solver.assertions())
opt.maximize(num_met)

if opt.check() == sat:
    model = opt.model()
    itinerary = []
    for i in range(n):
        if is_true(model[met[i]]):
            name = friends[i][0]
            start_val = model[s[i]].as_long()
            end_val = model[e[i]].as_long()
            start_hour = start_val // 60
            start_minute = start_val % 60
            end_hour = end_val // 60
            end_minute = end_val % 60
            start_time_str = f"{start_hour:02d}:{start_minute:02d}"
            end_time_str = f"{end_hour:02d}:{end_minute:02d}"
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_time_str,
                "end_time": end_time_str
            })
    itinerary.sort(key=lambda x: x['start_time'])
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(result)
else:
    print("No solution found")