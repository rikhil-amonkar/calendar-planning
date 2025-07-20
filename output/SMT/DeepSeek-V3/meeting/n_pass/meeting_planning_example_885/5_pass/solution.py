from z3 import *
import json

def solve_scheduling_problem():
    s = Optimize()

    # Friends data
    friends = {
        "Mark": {"location": "Marina District", "start": "18:45", "end": "21:00", "min_duration": 90},
        "Karen": {"location": "Financial District", "start": "09:30", "end": "12:45", "min_duration": 90},
        "Barbara": {"location": "Alamo Square", "start": "10:00", "end": "19:30", "min_duration": 90},
        "Nancy": {"location": "Golden Gate Park", "start": "16:45", "end": "20:00", "min_duration": 105},
        "David": {"location": "The Castro", "start": "09:00", "end": "18:00", "min_duration": 120},
        "Linda": {"location": "Bayview", "start": "18:15", "end": "19:45", "min_duration": 45},
        "Kevin": {"location": "Sunset District", "start": "10:00", "end": "17:45", "min_duration": 120},
        "Matthew": {"location": "Haight-Ashbury", "start": "10:15", "end": "15:30", "min_duration": 45},
        "Andrew": {"location": "Nob Hill", "start": "11:45", "end": "16:45", "min_duration": 105}
    }

    # Helper functions to convert time
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Travel times dictionary (from the problem statement)
    travel_times = {
        "Russian Hill": {
            "Marina District": 7,
            "Financial District": 11,
            "Alamo Square": 15,
            "Golden Gate Park": 21,
            "The Castro": 21,
            "Bayview": 23,
            "Sunset District": 23,
            "Haight-Ashbury": 17,
            "Nob Hill": 5
        },
        "Marina District": {
            "Russian Hill": 8,
            "Financial District": 17,
            "Alamo Square": 15,
            "Golden Gate Park": 18,
            "The Castro": 22,
            "Bayview": 27,
            "Sunset District": 19,
            "Haight-Ashbury": 16,
            "Nob Hill": 12
        },
        "Financial District": {
            "Russian Hill": 11,
            "Marina District": 15,
            "Alamo Square": 17,
            "Golden Gate Park": 23,
            "The Castro": 20,
            "Bayview": 19,
            "Sunset District": 30,
            "Haight-Ashbury": 19,
            "Nob Hill": 8
        },
        "Alamo Square": {
            "Russian Hill": 13,
            "Marina District": 15,
            "Financial District": 17,
            "Golden Gate Park": 9,
            "The Castro": 8,
            "Bayview": 16,
            "Sunset District": 16,
            "Haight-Ashbury": 5,
            "Nob Hill": 11
        },
        "Golden Gate Park": {
            "Russian Hill": 19,
            "Marina District": 16,
            "Financial District": 26,
            "Alamo Square": 9,
            "The Castro": 13,
            "Bayview": 23,
            "Sunset District": 10,
            "Haight-Ashbury": 7,
            "Nob Hill": 20
        },
        "The Castro": {
            "Russian Hill": 18,
            "Marina District": 21,
            "Financial District": 21,
            "Alamo Square": 8,
            "Golden Gate Park": 11,
            "Bayview": 19,
            "Sunset District": 17,
            "Haight-Ashbury": 6,
            "Nob Hill": 16
        },
        "Bayview": {
            "Russian Hill": 23,
            "Marina District": 27,
            "Financial District": 19,
            "Alamo Square": 16,
            "Golden Gate Park": 22,
            "The Castro": 19,
            "Sunset District": 23,
            "Haight-Ashbury": 19,
            "Nob Hill": 20
        },
        "Sunset District": {
            "Russian Hill": 24,
            "Marina District": 21,
            "Financial District": 30,
            "Alamo Square": 17,
            "Golden Gate Park": 11,
            "The Castro": 17,
            "Bayview": 22,
            "Haight-Ashbury": 15,
            "Nob Hill": 27
        },
        "Haight-Ashbury": {
            "Russian Hill": 17,
            "Marina District": 17,
            "Financial District": 21,
            "Alamo Square": 5,
            "Golden Gate Park": 7,
            "The Castro": 6,
            "Bayview": 18,
            "Sunset District": 15,
            "Nob Hill": 15
        },
        "Nob Hill": {
            "Russian Hill": 5,
            "Marina District": 11,
            "Financial District": 9,
            "Alamo Square": 11,
            "Golden Gate Park": 17,
            "The Castro": 17,
            "Bayview": 19,
            "Sunset District": 24,
            "Haight-Ashbury": 13
        }
    }

    def get_travel_time(from_loc, to_loc):
        return travel_times.get(from_loc, {}).get(to_loc, 0)

    # Create meeting variables
    meetings = {}
    for name in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        meetings[name] = {
            'start': start_var,
            'end': end_var,
            'location': friends[name]['location'],
            'min_duration': friends[name]['min_duration'],
            'available_start': time_to_minutes(friends[name]['start']),
            'available_end': time_to_minutes(friends[name]['end'])
        }
        s.add(start_var >= meetings[name]['available_start'])
        s.add(end_var <= meetings[name]['available_end'])
        s.add(end_var == start_var + meetings[name]['min_duration'])

    # Current location and time
    current_location = "Russian Hill"
    current_time = 540  # 9:00 AM

    # To model the sequence, we'll assume an arbitrary order and add constraints
    # that for any two meetings, one must be after the other plus travel time
    meeting_names = list(meetings.keys())
    for i in range(len(meeting_names)):
        for j in range(i + 1, len(meeting_names)):
            name1 = meeting_names[i]
            name2 = meeting_names[j]
            loc1 = meetings[name1]['location']
            loc2 = meetings[name2]['location']
            travel_time = get_travel_time(loc1, loc2)
            # Either meeting1 is before meeting2 with travel time
            before = And(
                meetings[name1]['end'] + travel_time <= meetings[name2]['start']
            )
            # Or meeting2 is before meeting1 with travel time from loc2 to loc1
            travel_time_reverse = get_travel_time(loc2, loc1)
            after = And(
                meetings[name2]['end'] + travel_time_reverse <= meetings[name1]['start']
            )
            s.add(Or(before, after))

    # Also, all meetings must start after current_time (9:00 AM) plus travel time from Russian Hill
    for name in meetings:
        loc = meetings[name]['location']
        travel_time = get_travel_time(current_location, loc)
        s.add(meetings[name]['start'] >= current_time + travel_time)

    # Maximize the number of meetings
    meeting_active = {}
    for name in meetings:
        active = Bool(f'active_{name}')
        meeting_active[name] = active
        s.add(active == (meetings[name]['start'] >= current_time))

    s.maximize(Sum([If(active, 1, 0) for active in meeting_active.values()]))

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in meetings:
            if model[meeting_active[name]]:
                start_val = model[meetings[name]['start']].as_long()
                end_val = model[meetings[name]['end']].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val)
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x['start_time']))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the solver and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))