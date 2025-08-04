from z3 import *
import json

def solve_scheduling():
    opt = Optimize()

    # Define friends and their availability (times in minutes since midnight)
    friends = {
        "Steven": {"location": "North Beach", "start": 1050, "end": 1230, "duration": 15},
        "Sarah": {"location": "Golden Gate Park", "start": 1020, "end": 1155, "duration": 75},
        "Brian": {"location": "Embarcadero", "start": 855, "end": 960, "duration": 105},
        "Stephanie": {"location": "Haight-Ashbury", "start": 615, "end": 735, "duration": 75},
        "Melissa": {"location": "Richmond District", "start": 840, "end": 1170, "duration": 30},
        "Nancy": {"location": "Nob Hill", "start": 495, "end": 765, "duration": 90},
        "David": {"location": "Marina District", "start": 675, "end": 795, "duration": 120},
        "James": {"location": "Presidio", "start": 900, "end": 1035, "duration": 120},
        "Elizabeth": {"location": "Union Square", "start": 690, "end": 1260, "duration": 60},
        "Robert": {"location": "Financial District", "start": 795, "end": 915, "duration": 45}
    }

    # Travel times in minutes
    travel_times = {
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Financial District"): 21,
    }

    # Create meeting variables
    meetings = {}
    for name in friends:
        meetings[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'location': friends[name]['location'],
            'scheduled': Bool(f'scheduled_{name}')
        }

    # Base constraints
    for name in friends:
        info = friends[name]
        m = meetings[name]
        opt.add(Implies(m['scheduled'], m['start'] >= info['start']))
        opt.add(Implies(m['scheduled'], m['end'] <= info['end']))
        opt.add(Implies(m['scheduled'], m['end'] == m['start'] + info['duration']))
        opt.add(Implies(Not(m['scheduled']), m['start'] == -1))

    # Temporal constraints
    all_meetings = [(name, meetings[name]) for name in friends]
    for i in range(len(all_meetings)):
        name1, m1 = all_meetings[i]
        for j in range(i+1, len(all_meetings)):
            name2, m2 = all_meetings[j]
            
            # Either one meeting is not scheduled, or they don't overlap
            opt.add(Or(
                Not(m1['scheduled']),
                Not(m2['scheduled']),
                m1['end'] + travel_times.get((m1['location'], m2['location']), 0) <= m2['start'],
                m2['end'] + travel_times.get((m2['location'], m1['location']), 0) <= m1['start']
            ))

    # Starting point constraint (must start after 9:00 AM/540 minutes)
    opt.add(Or([And(meetings[name]['scheduled'], meetings[name]['start'] >= 540) for name in friends]))

    # Maximize number of meetings
    opt.maximize(Sum([If(meetings[name]['scheduled'], 1, 0) for name in friends]))

    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for name in friends:
            if m.evaluate(meetings[name]['scheduled']):
                start = m[meetings[name]['start']].as_long()
                end = m[meetings[name]['end']].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start//60:02d}:{start%60:02d}",
                    "end_time": f"{end//60:02d}:{end%60:02d}"
                })
        itinerary.sort(key=lambda x: int(x['start_time'].replace(':', '')))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

result = solve_scheduling()
print(json.dumps(result, indent=2))