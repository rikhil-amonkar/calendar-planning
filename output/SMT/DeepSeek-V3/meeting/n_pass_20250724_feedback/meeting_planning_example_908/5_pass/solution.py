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

    # Complete travel times matrix with all locations
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
        "Fisherman's Wharf": {
            "Financial District": 11,
            "Presidio": 17,
            "Bayview": 26,
            "Haight-Ashbury": 22,
            "Russian Hill": 7,
            "The Castro": 27,
            "Marina District": 9,
            "Richmond District": 18,
            "Union Square": 13,
            "Sunset District": 27
        },
        "Presidio": {
            "Financial District": 23,
            "Fisherman's Wharf": 19,
            "Bayview": 31,
            "Haight-Ashbury": 15,
            "Russian Hill": 14,
            "The Castro": 21,
            "Marina District": 11,
            "Richmond District": 7,
            "Union Square": 22,
            "Sunset District": 15
        },
        "Bayview": {
            "Financial District": 19,
            "Fisherman's Wharf": 25,
            "Presidio": 32,
            "Haight-Ashbury": 19,
            "Russian Hill": 23,
            "The Castro": 19,
            "Marina District": 27,
            "Richmond District": 25,
            "Union Square": 18,
            "Sunset District": 23
        },
        "Haight-Ashbury": {
            "Financial District": 21,
            "Fisherman's Wharf": 23,
            "Presidio": 15,
            "Bayview": 18,
            "Russian Hill": 17,
            "The Castro": 6,
            "Marina District": 17,
            "Richmond District": 10,
            "Union Square": 19,
            "Sunset District": 15
        },
        "Russian Hill": {
            "Financial District": 11,
            "Fisherman's Wharf": 7,
            "Presidio": 14,
            "Bayview": 23,
            "Haight-Ashbury": 17,
            "The Castro": 21,
            "Marina District": 7,
            "Richmond District": 14,
            "Union Square": 10,
            "Sunset District": 23
        },
        "The Castro": {
            "Financial District": 21,
            "Fisherman's Wharf": 24,
            "Presidio": 20,
            "Bayview": 19,
            "Haight-Ashbury": 6,
            "Russian Hill": 18,
            "Marina District": 21,
            "Richmond District": 16,
            "Union Square": 19,
            "Sunset District": 17
        },
        "Marina District": {
            "Financial District": 17,
            "Fisherman's Wharf": 10,
            "Presidio": 10,
            "Bayview": 27,
            "Haight-Ashbury": 16,
            "Russian Hill": 8,
            "The Castro": 22,
            "Richmond District": 11,
            "Union Square": 16,
            "Sunset District": 19
        },
        "Richmond District": {
            "Financial District": 22,
            "Fisherman's Wharf": 18,
            "Presidio": 7,
            "Bayview": 27,
            "Haight-Ashbury": 10,
            "Russian Hill": 13,
            "The Castro": 16,
            "Marina District": 9,
            "Union Square": 21,
            "Sunset District": 11
        },
        "Union Square": {
            "Financial District": 9,
            "Fisherman's Wharf": 15,
            "Presidio": 24,
            "Bayview": 15,
            "Haight-Ashbury": 18,
            "Russian Hill": 13,
            "The Castro": 17,
            "Marina District": 18,
            "Richmond District": 20,
            "Sunset District": 27
        },
        "Sunset District": {
            "Financial District": 30,
            "Fisherman's Wharf": 29,
            "Presidio": 16,
            "Bayview": 22,
            "Haight-Ashbury": 15,
            "Russian Hill": 24,
            "The Castro": 17,
            "Marina District": 21,
            "Richmond District": 12,
            "Union Square": 30
        }
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
                # Get travel time, default to 0 if not found (shouldn't happen with complete matrix)
                travel_time = travel_times.get(loc1, {}).get(loc2, 0)

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