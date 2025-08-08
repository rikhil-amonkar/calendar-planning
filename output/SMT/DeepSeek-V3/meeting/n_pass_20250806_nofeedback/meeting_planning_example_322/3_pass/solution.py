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

    travel_times = [
        [0, 24, 30, 16, 29],    # Sunset District to others
        [23, 0, 9, 14, 7],      # Russian Hill to others
        [29, 7, 0, 19, 8],      # Chinatown to others
        [15, 14, 21, 0, 19],    # Presidio to others
        [27, 7, 12, 17, 0]      # Fisherman's Wharf to others
    ]

    # Friends' availability (converted to minutes since 9:00 AM)
    friends = {
        'William': {'location': 'Russian Hill', 'start': 570, 'end': 645, 'min_duration': 105},
        'Michelle': {'location': 'Chinatown', 'start': -45, 'end': 300, 'min_duration': 15},
        'George': {'location': 'Presidio', 'start': 90, 'end': 525, 'min_duration': 30},
        'Robert': {'location': 'Fisherman\'s Wharf', 'start': 0, 'end': 285, 'min_duration': 30}
    }

    # Variables
    meet_start = {name: Int(f'meet_start_{name}') for name in friends}
    meet_end = {name: Int(f'meet_end_{name}') for name in friends}
    meet_duration = {name: Int(f'meet_duration_{name}') for name in friends}
    meet_order = {name: Int(f'meet_order_{name}') for name in friends}

    # Constraints
    for name in friends:
        # Duration constraints
        opt.add(meet_duration[name] == meet_end[name] - meet_start[name])
        opt.add(meet_duration[name] >= friends[name]['min_duration'])
        
        # Availability constraints
        opt.add(meet_start[name] >= friends[name]['start'])
        opt.add(meet_end[name] <= friends[name]['end'])
        
        # Can't meet before arriving at Sunset District at 9:00 AM (time 0)
        opt.add(meet_start[name] >= 0)

    # Meeting ordering constraints
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                # Either name1 is before name2 or vice versa
                opt.add(Or(
                    And(meet_order[name1] < meet_order[name2], meet_end[name1] + travel_times[locations[friends[name1]['location']]][locations[friends[name2]['location']]] <= meet_start[name2]),
                    And(meet_order[name2] < meet_order[name1], meet_end[name2] + travel_times[locations[friends[name2]['location']]][locations[friends[name1]['location']]] <= meet_start[name1])
                ))

    # Objective: maximize number of meetings (simpler than maximizing duration)
    opt.maximize(Sum([If(meet_duration[name] >= friends[name]['min_duration'], 1, 0) for name in friends]))

    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for name in friends:
            if m[meet_duration[name]].as_long() >= friends[name]['min_duration']:
                start = m[meet_start[name]].as_long()
                end = m[meet_end[name]].as_long()
                
                # Convert minutes since 9:00 AM to HH:MM
                def to_hhmm(minutes):
                    time = datetime(2023, 1, 1, 9, 0) + timedelta(minutes=minutes)
                    return time.strftime("%H:%M")
                
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