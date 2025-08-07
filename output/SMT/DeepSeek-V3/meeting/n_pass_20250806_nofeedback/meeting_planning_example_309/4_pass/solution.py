from z3 import *
import json

def solve_scheduling():
    opt = Optimize()

    # Locations and travel times (in minutes)
    locations = {
        'Financial District': 0,
        'Chinatown': 1,
        'Alamo Square': 2,
        'Bayview': 3,
        'Fisherman\'s Wharf': 4
    }

    travel_times = [
        [0, 5, 17, 19, 10],
        [5, 0, 17, 22, 8],
        [17, 16, 0, 16, 19],
        [19, 18, 16, 0, 25],
        [11, 12, 20, 26, 0]
    ]

    # Friends data
    friends = [
        {'name': 'Nancy', 'location': 'Chinatown', 'available_start': 9.5, 'available_end': 13.5, 'duration': 1.5},
        {'name': 'Mary', 'location': 'Alamo Square', 'available_start': 7.0, 'available_end': 21.0, 'duration': 1.25},
        {'name': 'Jessica', 'location': 'Bayview', 'available_start': 11.25, 'available_end': 13.75, 'duration': 0.75},
        {'name': 'Rebecca', 'location': 'Fisherman\'s Wharf', 'available_start': 7.0, 'available_end': 8.5, 'duration': 0.75}
    ]

    # Create meeting variables
    meetings = []
    for friend in friends:
        start = Real(f"start_{friend['name']}")
        end = Real(f"end_{friend['name']}")
        met = Bool(f"met_{friend['name']}")
        loc = locations[friend['location']]
        meetings.append({
            'name': friend['name'],
            'start': start,
            'end': end,
            'met': met,
            'loc': loc,
            'duration': friend['duration'],
            'avail_start': friend['available_start'],
            'avail_end': friend['available_end']
        })

    # Current state
    current_loc = locations['Financial District']
    current_time = 9.0  # 9:00 AM

    # Constraints
    for m in meetings:
        # If meeting happens, it must be within availability window
        opt.add(Implies(m['met'], And(
            m['start'] >= m['avail_start'],
            m['end'] <= m['avail_end'],
            m['end'] == m['start'] + m['duration']
        )))

    # Temporal constraints (no overlaps + travel time)
    for i in range(len(meetings)):
        for j in range(i+1, len(meetings)):
            # Either i before j or j before i, with travel time
            travel_ij = travel_times[meetings[i]['loc']][meetings[j]['loc']]/60
            travel_ji = travel_times[meetings[j]['loc']][meetings[i]['loc']]/60
            
            opt.add(Implies(And(meetings[i]['met'], meetings[j]['met']),
                Or(
                    meetings[i]['end'] + travel_ij <= meetings[j]['start'],
                    meetings[j]['end'] + travel_ji <= meetings[i]['start']
                )
            ))

    # Must start from Financial District at 9:00 AM
    first_meeting = Real("first_meeting_time")
    opt.add(Or(
        And([Not(m['met']) for m in meetings]),  # No meetings at all
        Or([And(
            m['met'],
            first_meeting == m['start'],
            first_meeting >= current_time + travel_times[current_loc][m['loc']]/60
        ) for m in meetings])
    ))

    # Objective: maximize number of meetings
    opt.maximize(Sum([If(m['met'], 1, 0) for m in meetings]))

    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for m in meetings:
            if is_true(model[m['met']]):
                start_val = model[m['start']].as_fraction()
                end_val = model[m['end']].as_fraction()
                
                start_h = int(start_val.numerator / start_val.denominator)
                start_m = int((start_val.numerator % start_val.denominator) * 60 / start_val.denominator)
                end_h = int(end_val.numerator / end_val.denominator)
                end_m = int((end_val.numerator % end_val.denominator) * 60 / end_val.denominator)
                
                itinerary.append({
                    "action": "meet",
                    "person": m['name'],
                    "start_time": f"{start_h:02d}:{start_m:02d}",
                    "end_time": f"{end_h:02d}:{end_m:02d}"
                })
        
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

result = solve_scheduling()
print(json.dumps(result, indent=2))