from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their constraints with priority weights
    friends = {
        "Mark": {"location": "Fisherman's Wharf", "available_start": "8:15", "available_end": "10:00", "duration": 30, "priority": 1},
        "Stephanie": {"location": "Presidio", "available_start": "12:15", "available_end": "15:00", "duration": 75, "priority": 3},
        "Betty": {"location": "Bayview", "available_start": "7:15", "available_end": "20:30", "duration": 15, "priority": 1},
        "Lisa": {"location": "Haight-Ashbury", "available_start": "15:30", "available_end": "18:30", "duration": 45, "priority": 2},
        "William": {"location": "Russian Hill", "available_start": "18:45", "available_end": "20:00", "duration": 60, "priority": 2},
        "Brian": {"location": "The Castro", "available_start": "9:15", "available_end": "13:15", "duration": 30, "priority": 1},
        "Joseph": {"location": "Marina District", "available_start": "10:45", "available_end": "15:00", "duration": 90, "priority": 3},
        "Ashley": {"location": "Richmond District", "available_start": "9:45", "available_end": "11:15", "duration": 45, "priority": 2},
        "Patricia": {"location": "Union Square", "available_start": "16:30", "available_end": "20:00", "duration": 120, "priority": 4},
        "Karen": {"location": "Sunset District", "available_start": "16:30", "available_end": "22:00", "duration": 105, "priority": 4}
    }

    # Travel times between locations (in minutes)
    travel_times = {
        "Financial District": {
            "Fisherman's Wharf": 10,
            "Presidio": 22,
            "Bayview": 19,
            "Haight-Ashbury": 19,
            "Russian Hill": 11,
            "The Castro": 20,
            "Marina District": 15,
            "Richmond District": 21,
            "Union Square": 9,
            "Sunset District": 30
        },
        # ... (rest of travel times remain the same as previous)
    }

    # Helper functions for time conversion
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = (minutes // 60) % 24
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Initialize variables
    meeting_vars = {}
    for name in friends:
        meeting_vars[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'met': Bool(f'met_{name}')
        }

    # Base constraints
    for name in friends:
        friend = friends[name]
        start_min = time_to_minutes(friend['available_start'])
        end_min = time_to_minutes(friend['available_end'])
        duration = friend['duration']

        # If meeting happens, it must fit within availability
        s.add(Implies(meeting_vars[name]['met'],
              And(meeting_vars[name]['start'] >= start_min,
                  meeting_vars[name]['end'] <= end_min,
                  meeting_vars[name]['end'] == meeting_vars[name]['start'] + duration)))

        # If not meeting, set times to 0
        s.add(Implies(Not(meeting_vars[name]['met']),
              And(meeting_vars[name]['start'] == 0,
                  meeting_vars[name]['end'] == 0)))

    # Arrival time constraint
    arrival_time = time_to_minutes("9:00")
    for name in friends:
        s.add(Implies(meeting_vars[name]['met'],
              meeting_vars[name]['start'] >= arrival_time))

    # No overlapping meetings with travel time
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                loc1 = friends[name1]['location']
                loc2 = friends[name2]['location']
                travel_time = travel_times[loc1].get(loc2, 0)

                s.add(Implies(And(meeting_vars[name1]['met'], meeting_vars[name2]['met']),
                      Or(meeting_vars[name1]['end'] + travel_time <= meeting_vars[name2]['start'],
                         meeting_vars[name2]['end'] + travel_time <= meeting_vars[name1]['start'])))

    # Optimization: maximize priority-weighted meetings
    total_priority = Int('total_priority')
    s.add(total_priority == Sum([If(meeting_vars[name]['met'], friends[name]['priority'], 0) 
                               for name in friends]))

    # Find solution that maximizes total priority
    maximize(s, total_priority)

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in friends:
            if is_true(model[meeting_vars[name]['met']]):
                start_time = model[meeting_vars[name]['start']].as_long()
                end_time = model[meeting_vars[name]['end']].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })
        # Sort by start time
        itinerary.sort(key=lambda x: time_to_minutes(x['start_time']))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))