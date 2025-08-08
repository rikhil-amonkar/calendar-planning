from z3 import *
import json
from datetime import datetime, timedelta

def solve_scheduling():
    opt = Optimize()

    # Locations and travel times (in minutes)
    locations = {
        'Sunset District': 0,
        'Russian Hill': 1,
        'Chinatown': 2,
        'Presidio': 3,
        'Fisherman\'s Wharf': 4
    }
    loc_names = ['Sunset District', 'Russian Hill', 'Chinatown', 'Presidio', 'Fisherman\'s Wharf']

    travel_times = [
        [0, 24, 30, 16, 29],    # Sunset District to others
        [23, 0, 9, 14, 7],      # Russian Hill to others
        [29, 7, 0, 19, 8],      # Chinatown to others
        [15, 14, 21, 0, 19],    # Presidio to others
        [27, 7, 12, 17, 0]      # Fisherman's Wharf to others
    ]

    # Friends' availability (in minutes since midnight)
    friends = {
        'William': {'location': 'Russian Hill', 'start': 1110, 'end': 1245, 'min_duration': 105},
        'Michelle': {'location': 'Chinatown', 'start': 495, 'end': 840, 'min_duration': 15},
        'George': {'location': 'Presidio', 'start': 630, 'end': 1125, 'min_duration': 30},
        'Robert': {'location': 'Fisherman\'s Wharf', 'start': 540, 'end': 825, 'min_duration': 30}
    }

    # Variables
    meet_start = {name: Int(f'meet_start_{name}') for name in friends}
    meet_end = {name: Int(f'meet_end_{name}') for name in friends}
    meet_loc = {name: locations[friends[name]['location']] for name in friends}
    meet_order = {name: Int(f'meet_order_{name}') for name in friends}
    meets = {name: Bool(f'meets_{name}') for name in friends}  # Whether we meet this friend

    # Current time starts at 9:00 AM (540 minutes)
    current_time = 540
    current_loc = locations['Sunset District']

    # Constraints
    for name in friends:
        # If we meet this friend, enforce duration and availability
        opt.add(Implies(meets[name], 
                      And(meet_start[name] >= friends[name]['start'],
                          meet_end[name] <= friends[name]['end'],
                          meet_end[name] - meet_start[name] >= friends[name]['min_duration'],
                          meet_start[name] >= current_time)))

    # Meeting ordering constraints
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                # If we meet both, they must be properly ordered with travel time
                opt.add(Implies(And(meets[name1], meets[name2]),
                              Or(
                                  And(meet_order[name1] < meet_order[name2],
                                      meet_end[name1] + travel_times[meet_loc[name1]][meet_loc[name2]] <= meet_start[name2]),
                                  And(meet_order[name2] < meet_order[name1],
                                      meet_end[name2] + travel_times[meet_loc[name2]][meet_loc[name1]] <= meet_start[name1])
                              )))

    # Objective: maximize number of meetings
    opt.maximize(Sum([If(meets[name], 1, 0) for name in friends]))

    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for name in friends:
            if m[meets[name]]:
                start = m[meet_start[name]].as_long()
                end = m[meet_end[name]].as_long()
                
                # Convert minutes since midnight to HH:MM
                def to_hhmm(minutes):
                    h = minutes // 60
                    m = minutes % 60
                    return f"{h:02d}:{m:02d}"
                
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": to_hhmm(start),
                    "end_time": to_hhmm(end)
                })
        
        # Sort by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling()
print(json.dumps(solution, indent=2))