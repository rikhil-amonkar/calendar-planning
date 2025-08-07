import itertools
from z3 import *

# Hardcoded travel times between locations
travel_time_dict = {
    "Fisherman's Wharf": {
        "The Castro": 26,
        "Golden Gate Park": 25,
        "Embarcadero": 8,
        "Russian Hill": 7,
        "Nob Hill": 11,
        "Alamo Square": 20,
        "North Beach": 6
    },
    "The Castro": {
        "Fisherman's Wharf": 24,
        "Golden Gate Park": 11,
        "Embarcadero": 22,
        "Russian Hill": 18,
        "Nob Hill": 16,
        "Alamo Square": 8,
        "North Beach": 20
    },
    "Golden Gate Park": {
        "Fisherman's Wharf": 24,
        "The Castro": 13,
        "Embarcadero": 25,
        "Russian Hill": 19,
        "Nob Hill": 20,
        "Alamo Square": 10,
        "North Beach": 24
    },
    "Embarcadero": {
        "Fisherman's Wharf": 6,
        "The Castro": 25,
        "Golden Gate Park": 25,
        "Russian Hill": 8,
        "Nob Hill": 10,
        "Alamo Square": 19,
        "North Beach": 5
    },
    "Russian Hill": {
        "Fisherman's Wharf": 7,
        "The Castro": 21,
        "Golden Gate Park": 21,
        "Embarcadero": 8,
        "Nob Hill": 5,
        "Alamo Square": 15,
        "North Beach": 5
    },
    "Nob Hill": {
        "Fisherman's Wharf": 11,
        "The Castro": 17,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Russian Hill": 5,
        "Alamo Square": 11,
        "North Beach": 8
    },
    "Alamo Square": {
        "Fisherman's Wharf": 19,
        "The Castro": 8,
        "Golden Gate Park": 9,
        "Embarcadero": 17,
        "Russian Hill": 13,
        "Nob Hill": 11,
        "North Beach": 15
    },
    "North Beach": {
        "Fisherman's Wharf": 5,
        "The Castro": 22,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Russian Hill": 4,
        "Nob Hill": 7,
        "Alamo Square": 16
    }
}

# Friends data (excluding William and Stephanie)
friends = [
    {'name': 'Laura', 'location': 'The Castro', 'start_avail': 645, 'end_avail': 750, 'min_dur': 105},
    {'name': 'Daniel', 'location': 'Golden Gate Park', 'start_avail': 735, 'end_avail': 765, 'min_dur': 15},
    {'name': 'Karen', 'location': 'Russian Hill', 'start_avail': 330, 'end_avail': 645, 'min_dur': 30},
    {'name': 'Joseph', 'location': 'Alamo Square', 'start_avail': 150, 'end_avail': 225, 'min_dur': 15},
    {'name': 'Kimberly', 'location': 'North Beach', 'start_avail': 405, 'end_avail': 615, 'min_dur': 30}
]

def minutes_to_time(total_minutes_from_9am):
    total_minutes_from_midnight = 9 * 60 + total_minutes_from_9am
    hours = total_minutes_from_midnight // 60
    minutes = total_minutes_from_midnight % 60
    return f"{hours:02d}:{minutes:02d}"

# Try combinations from largest to smallest
solution_found = False
solution_comb = None
solution_model = None

for k in range(5, 0, -1):
    for comb in itertools.combinations(friends, k):
        s = Solver()
        start_vars = {}
        end_vars = {}
        order_vars = {}
        for friend in comb:
            name = friend['name']
            start_vars[name] = Int(f'start_{name}')
            end_vars[name] = Int(f'end_{name}')
            order_vars[name] = Int(f'order_{name}')
        
        # Constraints for availability and duration
        for friend in comb:
            name = friend['name']
            s.add(start_vars[name] >= friend['start_avail'])
            s.add(end_vars[name] == start_vars[name] + friend['min_dur'])
            s.add(end_vars[name] <= friend['end_avail'])
        
        # Order constraints: distinct and in [0, k-1]
        order_list = [order_vars[f['name']] for f in comb]
        s.add(Distinct(order_list))
        for ord_var in order_list:
            s.add(ord_var >= 0)
            s.add(ord_var < k)
        
        # Travel from start location to the first meeting
        for friend in comb:
            name = friend['name']
            loc = friend['location']
            travel_time = travel_time_dict['Fisherman\'s Wharf'][loc]
            s.add(If(order_vars[name] == 0, start_vars[name] >= travel_time, True))
        
        # Travel between consecutive meetings
        for i in comb:
            for j in comb:
                if i['name'] == j['name']:
                    continue
                loc_i = i['location']
                loc_j = j['location']
                travel_time_ij = travel_time_dict[loc_i][loc_j]
                s.add(If(order_vars[i['name']] < order_vars[j['name']], 
                         start_vars[j['name']] >= end_vars[i['name']] + travel_time_ij, 
                         True))
        
        if s.check() == sat:
            m = s.model()
            solution_found = True
            solution_comb = comb
            solution_model = m
            break
    if solution_found:
        break

itinerary = []
if solution_found:
    meetings = []
    for friend in solution_comb:
        name = friend['name']
        start_val = m.evaluate(start_vars[name]).as_long()
        end_val = m.evaluate(end_vars[name]).as_long()
        start_time_str = minutes_to_time(start_val)
        end_time_str = minutes_to_time(end_val)
        meetings.append({
            'start': start_val,
            'start_str': start_time_str,
            'end_str': end_time_str,
            'name': name
        })
    # Sort meetings by start time
    meetings_sorted = sorted(meetings, key=lambda x: x['start'])
    itinerary = [{"action": "meet", "person": m['name'], "start_time": m['start_str'], "end_time": m['end_str']} for m in meetings_sorted]

# Output the itinerary in JSON format
import json
output = {"itinerary": itinerary}
print("SOLUTION:")
print(json.dumps(output, indent=2))