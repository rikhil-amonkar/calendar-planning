from z3 import *
import json

def main():
    friends_data = [
        {"name": "Jeffrey", "location": "Fisherman's Wharf", "available_start": 75, "available_end": 240, "min_duration": 90},
        {"name": "Ronald", "location": "Alamo Square", "available_start": 0, "available_end": 345, "min_duration": 120},
        {"name": "Jason", "location": "Financial District", "available_start": 105, "available_end": 420, "min_duration": 105},
        {"name": "Melissa", "location": "Union Square", "available_start": 525, "available_end": 555, "min_duration": 15},
        {"name": "Elizabeth", "location": "Sunset District", "available_start": 345, "available_end": 510, "min_duration": 105},
        {"name": "Margaret", "location": "Embarcadero", "available_start": 255, "available_end": 600, "min_duration": 90},
        {"name": "George", "location": "Golden Gate Park", "available_start": 600, "available_end": 780, "min_duration": 75},
        {"name": "Richard", "location": "Chinatown", "available_start": 30, "available_end": 720, "min_duration": 15},
        {"name": "Laura", "location": "Richmond District", "available_start": 45, "available_end": 540, "min_duration": 60}
    ]
    
    travel_time = {
        'Presidio': {
            "Fisherman's Wharf": 19, "Alamo Square": 19, "Financial District": 23, "Union Square": 22,
            "Sunset District": 15, "Embarcadero": 20, "Golden Gate Park": 12, "Chinatown": 21, "Richmond District": 7
        },
        "Fisherman's Wharf": {
            'Presidio': 17, "Alamo Square": 21, "Financial District": 11, "Union Square": 13, "Sunset District": 27,
            "Embarcadero": 8, "Golden Gate Park": 25, "Chinatown": 12, "Richmond District": 18
        },
        "Alamo Square": {
            'Presidio': 17, "Fisherman's Wharf": 19, "Financial District": 17, "Union Square": 14, "Sunset District": 16,
            "Embarcadero": 16, "Golden Gate Park": 9, "Chinatown": 15, "Richmond District": 11
        },
        "Financial District": {
            'Presidio': 22, "Fisherman's Wharf": 10, "Alamo Square": 17, "Union Square": 9, "Sunset District": 30,
            "Embarcadero": 4, "Golden Gate Park": 23, "Chinatown": 5, "Richmond District": 21
        },
        "Union Square": {
            'Presidio': 24, "Fisherman's Wharf": 15, "Alamo Square": 15, "Financial District": 9, "Sunset District": 27,
            "Embarcadero": 11, "Golden Gate Park": 22, "Chinatown": 7, "Richmond District": 20
        },
        "Sunset District": {
            'Presidio': 16, "Fisherman's Wharf": 29, "Alamo Square": 17, "Financial District": 30, "Union Square": 30,
            "Embarcadero": 30, "Golden Gate Park": 11, "Chinatown": 30, "Richmond District": 12
        },
        "Embarcadero": {
            'Presidio': 20, "Fisherman's Wharf": 6, "Alamo Square": 19, "Financial District": 5, "Union Square": 10,
            "Sunset District": 30, "Golden Gate Park": 25, "Chinatown": 7, "Richmond District": 21
        },
        "Golden Gate Park": {
            'Presidio': 11, "Fisherman's Wharf": 24, "Alamo Square": 9, "Financial District": 26, "Union Square": 22,
            "Sunset District": 10, "Embarcadero": 25, "Chinatown": 23, "Richmond District": 7
        },
        "Chinatown": {
            'Presidio': 19, "Fisherman's Wharf": 8, "Alamo Square": 17, "Financial District": 5, "Union Square": 7,
            "Sunset District": 29, "Embarcadero": 5, "Golden Gate Park": 23, "Richmond District": 20
        },
        "Richmond District": {
            'Presidio': 7, "Fisherman's Wharf": 18, "Alamo Square": 13, "Financial District": 22, "Union Square": 21,
            "Sunset District": 11, "Embarcadero": 19, "Golden Gate Park": 9, "Chinatown": 20
        }
    }

    s = Optimize()
    n = len(friends_data)
    include = [Bool(f'include_{i}') for i in range(n)]
    start = [Int(f'start_{i}') for i in range(n)]
    end = [Int(f'end_{i}') for i in range(n)]
    order = [Int(f'order_{i}') for i in range(n)]
    
    k = Sum([If(include[i], 1, 0) for i in range(n)])
    
    for i, friend in enumerate(friends_data):
        s.add(If(include[i],
                 And(
                     start[i] >= friend["available_start"],
                     end[i] <= friend["available_end"],
                     end[i] == start[i] + friend["min_duration"],
                     order[i] >= 0,
                     order[i] < n
                 ),
                 And(
                     start[i] == 0,
                     end[i] == 0,
                     order[i] == -1
                 )))
    
    for i in range(n):
        for j in range(i + 1, n):
            s.add(Implies(And(include[i], include[j]), order[i] != order[j]))
    
    s.add(Or([And(include[i], order[i] == 0) for i in range(n)]))
    
    for t in range(1, n):
        s.add(Implies(Or([And(include[i], order[i] == t) for i in range(n)]),
                     Or([And(include[j], order[j] == t - 1) for j in range(n)])))
    
    for i, friend in enumerate(friends_data):
        loc = friend["location"]
        time_from_start = travel_time['Presidio'][loc]
        s.add(If(And(include[i], order[i] == 0), start[i] >= time_from_start, True))
    
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            loc_i = friends_data[i]["location"]
            loc_j = friends_data[j]["location"]
            travel_ij = travel_time[loc_i][loc_j]
            s.add(If(And(include[i], include[j], order[j] == order[i] + 1),
                     start[j] >= end[i] + travel_ij,
                     True))
    
    s.maximize(k)
    
    itinerary = []
    if s.check() == sat:
        m = s.model()
        included_indices = []
        for i in range(n):
            if is_true(m.evaluate(include[i])):
                included_indices.append(i)
        
        meetings = []
        for i in included_indices:
            start_val = m.evaluate(start[i])
            end_val = m.evaluate(end[i])
            if isinstance(start_val, IntNumRef) and isinstance(end_val, IntNumRef):
                start_min = start_val.as_long()
                end_min = end_val.as_long()
                hours_start = 9 + start_min // 60
                minutes_start = start_min % 60
                hours_end = 9 + end_min // 60
                minutes_end = end_min % 60
                start_str = f"{hours_start:02d}:{minutes_start:02d}"
                end_str = f"{hours_end:02d}:{minutes_end:02d}"
                meetings.append({
                    "action": "meet",
                    "person": friends_data[i]["name"],
                    "start_time": start_str,
                    "end_time": end_str
                })
        meetings.sort(key=lambda x: x['start_time'])
        itinerary = meetings
    else:
        itinerary = []
    
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result))

if __name__ == "__main__":
    main()