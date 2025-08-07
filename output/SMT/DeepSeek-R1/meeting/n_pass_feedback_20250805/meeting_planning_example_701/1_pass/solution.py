from z3 import *
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    friends = ['Daniel', 'Betty', 'Kevin', 'Timothy', 'Steven', 'Lisa', 'Ashley', 'Elizabeth']
    
    locations = {
        'Daniel': 'Nob Hill',
        'Betty': 'Richmond District',
        'Kevin': 'Chinatown',
        'Timothy': 'Pacific Heights',
        'Steven': 'Marina District',
        'Lisa': 'The Castro',
        'Ashley': 'Golden Gate Park',
        'Elizabeth': 'Presidio'
    }
    
    min_durations = {
        'Daniel': 15,
        'Betty': 30,
        'Kevin': 30,
        'Timothy': 90,
        'Steven': 90,
        'Lisa': 120,
        'Ashley': 60,
        'Elizabeth': 45
    }
    
    windows = {
        'Daniel': (8*60+15, 11*60),         # 8:15AM to 11:00AM
        'Betty': (13*60+15, 15*60+45),       # 1:15PM to 3:45PM
        'Kevin': (12*60, 19*60),             # 12:00PM to 7:00PM
        'Timothy': (12*60, 18*60),           # 12:00PM to 6:00PM
        'Steven': (16*60+30, 20*60+45),      # 4:30PM to 8:45PM
        'Lisa': (19*60+15, 21*60+15),        # 7:15PM to 9:15PM
        'Ashley': (20*60+45, 21*60+45),      # 8:45PM to 9:45PM
        'Elizabeth': (21*60+15, 22*60+15)    # 9:15PM to 10:15PM
    }
    
    travel_time_dict = {
        'Mission District': {
            'The Castro': 7,
            'Nob Hill': 12,
            'Presidio': 25,
            'Marina District': 19,
            'Pacific Heights': 16,
            'Golden Gate Park': 17,
            'Chinatown': 16,
            'Richmond District': 20
        },
        'The Castro': {
            'Mission District': 7,
            'Nob Hill': 16,
            'Presidio': 20,
            'Marina District': 21,
            'Pacific Heights': 16,
            'Golden Gate Park': 11,
            'Chinatown': 22,
            'Richmond District': 16
        },
        'Nob Hill': {
            'Mission District': 13,
            'The Castro': 17,
            'Presidio': 17,
            'Marina District': 11,
            'Pacific Heights': 8,
            'Golden Gate Park': 17,
            'Chinatown': 6,
            'Richmond District': 14
        },
        'Presidio': {
            'Mission District': 26,
            'The Castro': 21,
            'Nob Hill': 18,
            'Marina District': 11,
            'Pacific Heights': 11,
            'Golden Gate Park': 12,
            'Chinatown': 21,
            'Richmond District': 7
        },
        'Marina District': {
            'Mission District': 20,
            'The Castro': 22,
            'Nob Hill': 12,
            'Presidio': 10,
            'Pacific Heights': 7,
            'Golden Gate Park': 18,
            'Chinatown': 15,
            'Richmond District': 11
        },
        'Pacific Heights': {
            'Mission District': 15,
            'The Castro': 16,
            'Nob Hill': 8,
            'Presidio': 11,
            'Marina District': 6,
            'Golden Gate Park': 15,
            'Chinatown': 11,
            'Richmond District': 12
        },
        'Golden Gate Park': {
            'Mission District': 17,
            'The Castro': 13,
            'Nob Hill': 20,
            'Presidio': 11,
            'Marina District': 16,
            'Pacific Heights': 16,
            'Chinatown': 23,
            'Richmond District': 7
        },
        'Chinatown': {
            'Mission District': 17,
            'The Castro': 22,
            'Nob Hill': 9,
            'Presidio': 19,
            'Marina District': 12,
            'Pacific Heights': 10,
            'Golden Gate Park': 23,
            'Richmond District': 20
        },
        'Richmond District': {
            'Mission District': 20,
            'The Castro': 16,
            'Nob Hill': 17,
            'Presidio': 7,
            'Marina District': 9,
            'Pacific Heights': 10,
            'Golden Gate Park': 9,
            'Chinatown': 20
        }
    }
    
    s = Optimize()
    
    meet_vars = {f: Bool(f'meet_{f}') for f in friends}
    start_vars = {f: Real(f'start_{f}') for f in friends}
    
    # Starting at Mission District at 9:00 AM (540 minutes from midnight)
    start_time_mission = 540
    
    # For each friend, if we meet them, enforce time window and travel time from Mission District
    for f in friends:
        loc = locations[f]
        travel_from_mission = travel_time_dict['Mission District'][loc]
        s.add(Implies(meet_vars[f], start_vars[f] >= windows[f][0]))
        s.add(Implies(meet_vars[f], start_vars[f] + min_durations[f] <= windows[f][1]))
        s.add(Implies(meet_vars[f], start_vars[f] >= start_time_mission + travel_from_mission))
    
    # For every pair of distinct friends, if both are met, enforce disjunctive constraint with travel time
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            f1 = friends[i]
            f2 = friends[j]
            loc1 = locations[f1]
            loc2 = locations[f2]
            travel_f1_to_f2 = travel_time_dict[loc1][loc2]
            travel_f2_to_f1 = travel_time_dict[loc2][loc1]
            both_met = And(meet_vars[f1], meet_vars[f2])
            disj = Or(
                start_vars[f2] >= start_vars[f1] + min_durations[f1] + travel_f1_to_f2,
                start_vars[f1] >= start_vars[f2] + min_durations[f2] + travel_f2_to_f1
            )
            s.add(Implies(both_met, disj))
    
    # Maximize the number of friends met
    total_meet = Sum([If(meet_vars[f], 1, 0) for f in friends])
    s.maximize(total_meet)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for f in friends:
            if m.eval(meet_vars[f]):
                start_val = m.eval(start_vars[f])
                # Convert Z3 rational to integer minutes
                if is_rational_value(start_val):
                    start_min = start_val.as_long()
                else:
                    start_min = int(str(start_val))
                end_min = start_min + min_durations[f]
                start_time_str = minutes_to_time(start_min)
                end_time_str = minutes_to_time(end_min)
                itinerary.append({
                    "action": "meet",
                    "person": f,
                    "start_time": start_time_str,
                    "end_time": end_time_str
                })
        # Sort itinerary by start_time
        itinerary.sort(key=lambda x: x['start_time'])
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()