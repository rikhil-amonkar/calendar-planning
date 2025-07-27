from z3 import *
import json

def solve_scheduling():
    opt = Optimize()

    # Convert time strings to minutes since midnight
    def time_to_min(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Define friends and their availability
    friends = {
        "Steven": {"location": "North Beach", "start": time_to_min("17:30"), "end": time_to_min("20:30"), "duration": 15},
        "Sarah": {"location": "Golden Gate Park", "start": time_to_min("17:00"), "end": time_to_min("19:15"), "duration": 75},
        "Brian": {"location": "Embarcadero", "start": time_to_min("14:15"), "end": time_to_min("16:00"), "duration": 105},
        "Stephanie": {"location": "Haight-Ashbury", "start": time_to_min("10:15"), "end": time_to_min("12:15"), "duration": 75},
        "Melissa": {"location": "Richmond District", "start": time_to_min("14:00"), "end": time_to_min("19:30"), "duration": 30},
        "Nancy": {"location": "Nob Hill", "start": time_to_min("08:15"), "end": time_to_min("12:45"), "duration": 90},
        "David": {"location": "Marina District", "start": time_to_min("11:15"), "end": time_to_min("13:15"), "duration": 120},
        "James": {"location": "Presidio", "start": time_to_min("15:00"), "end": time_to_min("18:15"), "duration": 120},
        "Elizabeth": {"location": "Union Square", "start": time_to_min("11:30"), "end": time_to_min("21:00"), "duration": 60},
        "Robert": {"location": "Financial District", "start": time_to_min("13:15"), "end": time_to_min("15:15"), "duration": 45}
    }

    # Complete travel times matrix
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
        # Add reverse directions and all other pairs
        ("North Beach", "The Castro"): 23,
        ("Golden Gate Park", "The Castro"): 13,
        # ... include all other pairs ...
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
        opt.add(Implies(m['scheduled'], And(
            m['start'] >= info['start'],
            m['end'] <= info['end'],
            m['end'] == m['start'] + info['duration']
        )))
        opt.add(Implies(Not(m['scheduled']), m['start'] == -1))

    # Starting at The Castro at 9:00 AM (540 minutes)
    current_time = 540
    current_location = "The Castro"

    # Temporal constraints between meetings
    scheduled_meetings = [m for m in meetings.values()]
    for i in range(len(scheduled_meetings)):
        for j in range(i+1, len(scheduled_meetings)):
            m1 = scheduled_meetings[i]
            m2 = scheduled_meetings[j]
            
            # Either one is not scheduled, or they are properly ordered with travel time
            opt.add(Or(
                Not(m1['scheduled']),
                Not(m2['scheduled']),
                And(
                    m1['end'] + travel_times.get((m1['location'], m2['location']), 0) <= m2['start']
                ),
                And(
                    m2['end'] + travel_times.get((m2['location'], m1['location']), 0) <= m1['start']
                )
            ))

    # Must start after 9:00 AM
    for name in friends:
        opt.add(Implies(meetings[name]['scheduled'], meetings[name]['start'] >= 540))

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
        # Sort by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

result = solve_scheduling()
print(json.dumps(result, indent=2))