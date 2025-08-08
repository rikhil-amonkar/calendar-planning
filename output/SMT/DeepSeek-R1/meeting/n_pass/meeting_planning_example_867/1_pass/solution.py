import z3
import json

def time_str_to_minutes_from_9am(s):
    time_part = s[:-2]
    period = s[-2:]
    hour, minute = map(int, time_part.split(':'))
    if period == "PM" and hour != 12:
        hour += 12
    if period == "AM" and hour == 12:
        hour = 0
    total_minutes_since_midnight = hour * 60 + minute
    base = 9 * 60
    result = total_minutes_since_midnight - base
    return max(result, 0)

travel_times = {
    "Haight-Ashbury": {
        "Mission District": 11,
        "Union Square": 19,
        "Pacific Heights": 12,
        "Bayview": 18,
        "Fisherman's Wharf": 23,
        "Marina District": 17,
        "Richmond District": 10,
        "Sunset District": 15,
        "Golden Gate Park": 7
    },
    "Mission District": {
        "Haight-Ashbury": 12,
        "Union Square": 15,
        "Pacific Heights": 16,
        "Bayview": 14,
        "Fisherman's Wharf": 22,
        "Marina District": 19,
        "Richmond District": 20,
        "Sunset District": 24,
        "Golden Gate Park": 17
    },
    "Union Square": {
        "Haight-Ashbury": 18,
        "Mission District": 14,
        "Pacific Heights": 15,
        "Bayview": 15,
        "Fisherman's Wharf": 15,
        "Marina District": 18,
        "Richmond District": 20,
        "Sunset District": 27,
        "Golden Gate Park": 22
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11,
        "Mission District": 15,
        "Union Square": 12,
        "Bayview": 22,
        "Fisherman's Wharf": 13,
        "Marina District": 6,
        "Richmond District": 12,
        "Sunset District": 21,
        "Golden Gate Park": 15
    },
    "Bayview": {
        "Haight-Ashbury": 19,
        "Mission District": 13,
        "Union Square": 18,
        "Pacific Heights": 23,
        "Fisherman's Wharf": 25,
        "Marina District": 27,
        "Richmond District": 25,
        "Sunset District": 23,
        "Golden Gate Park": 22
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Mission District": 22,
        "Union Square": 13,
        "Pacific Heights": 12,
        "Bayview": 26,
        "Marina District": 9,
        "Richmond District": 18,
        "Sunset District": 27,
        "Golden Gate Park": 25
    },
    "Marina District": {
        "Haight-Ashbury": 16,
        "Mission District": 20,
        "Union Square": 16,
        "Pacific Heights": 7,
        "Bayview": 27,
        "Fisherman's Wharf": 10,
        "Richmond District": 11,
        "Sunset District": 19,
        "Golden Gate Park": 18
    },
    "Richmond District": {
        "Haight-Ashbury": 10,
        "Mission District": 20,
        "Union Square": 21,
        "Pacific Heights": 10,
        "Bayview": 27,
        "Fisherman's Wharf": 18,
        "Marina District": 9,
        "Sunset District": 11,
        "Golden Gate Park": 9
    },
    "Sunset District": {
        "Haight-Ashbury": 15,
        "Mission District": 25,
        "Union Square": 30,
        "Pacific Heights": 21,
        "Bayview": 22,
        "Fisherman's Wharf": 29,
        "Marina District": 21,
        "Richmond District": 12,
        "Golden Gate Park": 11
    },
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Mission District": 17,
        "Union Square": 22,
        "Pacific Heights": 16,
        "Bayview": 23,
        "Fisherman's Wharf": 24,
        "Marina District": 16,
        "Richmond District": 7,
        "Sunset District": 10
    }
}

friends = [
    {"name": "Elizabeth", "location": "Mission District", "start_avail": "10:30AM", "end_avail": "8:00PM", "min_duration": 90},
    {"name": "David", "location": "Union Square", "start_avail": "3:15PM", "end_avail": "7:00PM", "min_duration": 45},
    {"name": "Sandra", "location": "Pacific Heights", "start_avail": "7:00AM", "end_avail": "8:00PM", "min_duration": 120},
    {"name": "Thomas", "location": "Bayview", "start_avail": "7:30PM", "end_avail": "8:30PM", "min_duration": 30},
    {"name": "Robert", "location": "Fisherman's Wharf", "start_avail": "10:00AM", "end_avail": "3:00PM", "min_duration": 15},
    {"name": "Kenneth", "location": "Marina District", "start_avail": "10:45AM", "end_avail": "1:00PM", "min_duration": 45},
    {"name": "Melissa", "location": "Richmond District", "start_avail": "6:15PM", "end_avail": "8:00PM", "min_duration": 15},
    {"name": "Kimberly", "location": "Sunset District", "start_avail": "10:15AM", "end_avail": "6:15PM", "min_duration": 105},
    {"name": "Amanda", "location": "Golden Gate Park", "start_avail": "7:45AM", "end_avail": "6:45PM", "min_duration": 15}
]

solver = z3.Optimize()
meet_vars = [z3.Bool(f"meet_{f['name']}") for f in friends]
start_vars = [z3.Real(f"start_{f['name']}") for f in friends]

for i, friend in enumerate(friends):
    start_min = time_str_to_minutes_from_9am(friend['start_avail'])
    end_max = time_str_to_minutes_from_9am(friend['end_avail'])
    min_duration = friend['min_duration']
    solver.add(z3.Implies(meet_vars[i], start_vars[i] >= start_min))
    solver.add(z3.Implies(meet_vars[i], start_vars[i] + min_duration <= end_max))
    
    travel_time = travel_times["Haight-Ashbury"][friend['location']]
    solver.add(z3.Implies(meet_vars[i], start_vars[i] >= travel_time))

for i in range(len(friends)):
    for j in range(i+1, len(friends)):
        if friends[i]['location'] == friends[j]['location']:
            continue
        loc_i = friends[i]['location']
        loc_j = friends[j]['location']
        travel_ij = travel_times[loc_i][loc_j]
        travel_ji = travel_times[loc_j][loc_i]
        dur_i = friends[i]['min_duration']
        dur_j = friends[j]['min_duration']
        solver.add(z3.Implies(z3.And(meet_vars[i], meet_vars[j]),
                             z3.Or(
                                 start_vars[i] + dur_i + travel_ij <= start_vars[j],
                                 start_vars[j] + dur_j + travel_ji <= start_vars[i]
                             )))

objective = z3.Sum([z3.If(b, 1, 0) for b in meet_vars])
solver.maximize(objective)

if solver.check() == z3.sat:
    model = solver.model()
    itinerary = []
    for i, friend in enumerate(friends):
        if z3.is_true(model[meet_vars[i]]):
            start_val = model[start_vars[i]]
            if isinstance(start_val, z3.RatNum):
                start_minutes = start_val.numerator_as_long() // start_val.denominator_as_long()
            else:
                start_minutes = start_val.as_long()
            total_minutes = int(start_minutes)
            dur = friend['min_duration']
            end_minutes = total_minutes + dur
            hour_start = 9 + total_minutes // 60
            minute_start = total_minutes % 60
            hour_end = 9 + end_minutes // 60
            minute_end = end_minutes % 60
            start_str = f"{hour_start:02d}:{minute_start:02d}"
            end_str = f"{hour_end:02d}:{minute_end:02d}"
            itinerary.append({
                "action": "meet",
                "person": friend['name'],
                "start_time": start_str,
                "end_time": end_str
            })
    itinerary_sorted = sorted(itinerary, key=lambda x: x['start_time'])
    result = {"itinerary": itinerary_sorted}
    print(json.dumps(result, indent=2))
else:
    print('{"itinerary": []}')