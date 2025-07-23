from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define locations and travel times
    locations = {
        'Financial District': 0,
        'Golden Gate Park': 1,
        'Chinatown': 2,
        'Union Square': 3,
        'Fisherman\'s Wharf': 4,
        'Pacific Heights': 5,
        'North Beach': 6
    }

    # Travel times matrix (from, to) -> minutes
    travel_times = {
        (0,1):23, (0,2):5, (0,3):9, (0,4):10, (0,5):13, (0,6):7,
        (1,0):26, (1,2):23, (1,3):22, (1,4):24, (1,5):16, (1,6):24,
        (2,0):5, (2,1):23, (2,3):7, (2,4):8, (2,5):10, (2,6):3,
        (3,0):9, (3,1):22, (3,2):7, (3,4):15, (3,5):15, (3,6):10,
        (4,0):11, (4,1):25, (4,2):12, (4,3):13, (4,5):12, (4,6):6,
        (5,0):13, (5,1):15, (5,2):11, (5,3):12, (5,4):13, (5,6):9,
        (6,0):8, (6,1):22, (6,2):6, (6,3):7, (6,4):5, (6,5):8
    }

    # Friends' availability
    friends = [
        {'name': 'Joseph', 'location': 'Pacific Heights', 'start': 8*60+15, 'end': 9*60+30, 'min_duration': 60},
        {'name': 'Rebecca', 'location': 'Fisherman\'s Wharf', 'start': 8*60, 'end': 11*60+15, 'min_duration': 30},
        {'name': 'Stephanie', 'location': 'Golden Gate Park', 'start': 11*60, 'end': 15*60, 'min_duration': 105},
        {'name': 'Karen', 'location': 'Chinatown', 'start': 13*60+45, 'end': 16*60+30, 'min_duration': 15},
        {'name': 'Steven', 'location': 'North Beach', 'start': 14*60+30, 'end': 20*60+45, 'min_duration': 120},
        {'name': 'Brian', 'location': 'Union Square', 'start': 15*60, 'end': 17*60+15, 'min_duration': 30}
    ]

    # Current location and time
    current_loc = locations['Financial District']
    current_time = 9 * 60

    # Create meeting variables
    meets = []
    for f in friends:
        start = Int(f"start_{f['name']}")
        end = Int(f"end_{f['name']}")
        duration = Int(f"dur_{f['name']}")
        loc = locations[f['location']]
        meets.append({
            'name': f['name'],
            'start': start,
            'end': end,
            'dur': duration,
            'loc': loc,
            'info': f
        })

    # Basic meeting constraints
    for m in meets:
        opt.add(m['start'] >= m['info']['start'])
        opt.add(m['end'] <= m['info']['end'])
        opt.add(m['dur'] >= m['info']['min_duration'])
        opt.add(m['end'] == m['start'] + m['dur'])

    # Meeting order and travel constraints
    # We'll use a sequence variable to determine meeting order
    seq = [Int(f"seq_{i}") for i in range(len(meets))]
    opt.add(Distinct(seq))
    for i in range(len(meets)):
        opt.add(seq[i] >= 0)
        opt.add(seq[i] < len(meets))

    # For each possible pair, ensure travel time is accounted for
    for i in range(len(meets)):
        for j in range(len(meets)):
            if i != j:
                opt.add(Implies(
                    seq[i] < seq[j],
                    meets[j]['start'] >= meets[i]['end'] + travel_times[(meets[i]['loc'], meets[j]['loc'])]
                ))

    # First meeting must be reachable from starting location
    for i in range(len(meets)):
        opt.add(Implies(
            seq[i] == 0,
            meets[i]['start'] >= current_time + travel_times[(current_loc, meets[i]['loc'])]
        ))

    # Try to meet as many friends as possible first
    met = [Int(f"met_{m['name']}") for m in meets]
    for i in range(len(meets)):
        opt.add(met[i] == If(meets[i]['dur'] >= meets[i]['info']['min_duration'], 1, 0))

    total_met = Int('total_met')
    opt.add(total_met == sum(met))
    opt.maximize(total_met)

    # Then maximize total time spent with friends
    total_dur = Int('total_dur')
    opt.add(total_dur == sum([m['dur'] for m in meets]))
    opt.maximize(total_dur)

    # Check solution
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for m in meets:
            s = model.evaluate(m['start']).as_long()
            e = model.evaluate(m['end']).as_long()
            if e - s >= m['info']['min_duration']:
                itinerary.append({
                    "action": "meet",
                    "person": m['name'],
                    "start_time": f"{s//60:02d}:{s%60:02d}",
                    "end_time": f"{e//60:02d}:{e%60:02d}"
                })
        # Sort by start time
        itinerary.sort(key=lambda x: (int(x['start_time'][:2]), int(x['start_time'][3:])))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))