from z3 import *
import json

def solve_scheduling():
    opt = Optimize()

    # Define friends and their details
    friends = [
        {"name": "Kevin", "location": "Mission District", "start": "20:45", "end": "21:45", "duration": 60},
        {"name": "Mark", "location": "Fisherman's Wharf", "start": "17:15", "end": "20:00", "duration": 90},
        {"name": "Jessica", "location": "Russian Hill", "start": "09:00", "end": "15:00", "duration": 120},
        {"name": "Jason", "location": "Marina District", "start": "15:15", "end": "21:45", "duration": 120},
        {"name": "John", "location": "North Beach", "start": "09:45", "end": "18:00", "duration": 15},
        {"name": "Karen", "location": "Chinatown", "start": "16:45", "end": "19:00", "duration": 75},
        {"name": "Sarah", "location": "Pacific Heights", "start": "17:30", "end": "18:15", "duration": 45},
        {"name": "Amanda", "location": "The Castro", "start": "20:00", "end": "21:15", "duration": 60},
        {"name": "Nancy", "location": "Nob Hill", "start": "09:45", "end": "13:00", "duration": 45},
        {"name": "Rebecca", "location": "Sunset District", "start": "08:45", "end": "15:00", "duration": 75}
    ]

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # 9:00 AM is 540 minutes

    def minutes_to_time(mins):
        total_mins = 540 + mins
        hh = total_mins // 60
        mm = total_mins % 60
        return f"{hh:02d}:{mm:02d}"

    # Create variables
    for friend in friends:
        friend['start_var'] = Int(f"start_{friend['name']}")
        friend['end_var'] = Int(f"end_{friend['name']}")
        friend['start_min'] = time_to_minutes(friend['start'])
        friend['end_min'] = time_to_minutes(friend['end'])
        friend['duration_min'] = friend['duration']
        friend['met'] = Bool(f"met_{friend['name']}")

    # Travel times dictionary (from_location, to_location) -> minutes
    travel_times = {
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "The Castro"): 17,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Sunset District"): 27,
        # Add reverse directions
        ("Mission District", "Union Square"): 14,
        ("Fisherman's Wharf", "Union Square"): 15,
        ("Russian Hill", "Union Square"): 13,
        ("Marina District", "Union Square"): 18,
        ("North Beach", "Union Square"): 10,
        ("Chinatown", "Union Square"): 7,
        ("Pacific Heights", "Union Square"): 15,
        ("The Castro", "Union Square"): 17,
        ("Nob Hill", "Union Square"): 9,
        ("Sunset District", "Union Square"): 27,
        # Add other connections
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        # Add more as needed
    }

    # Add basic meeting constraints
    for friend in friends:
        opt.add(Implies(friend['met'], friend['start_var'] >= friend['start_min']))
        opt.add(Implies(friend['met'], friend['end_var'] <= friend['end_min']))
        opt.add(Implies(friend['met'], friend['end_var'] == friend['start_var'] + friend['duration_min']))

    # Create a total order of meetings
    meeting_order = [Int(f"order_{friend['name']}") for friend in friends]
    opt.add(Distinct(meeting_order))
    for m in meeting_order:
        opt.add(m >= 0)
        opt.add(m < len(friends))

    # Add travel time constraints between consecutive meetings
    for i, friend1 in enumerate(friends):
        for j, friend2 in enumerate(friends):
            if i != j:
                travel_time = travel_times.get((friend1['location'], friend2['location']), 0)
                if travel_time > 0:  # Only add constraint if we know the travel time
                    opt.add(Implies(
                        And(friend1['met'], friend2['met'], meeting_order[i] + 1 == meeting_order[j]),
                        friend2['start_var'] >= friend1['end_var'] + travel_time
                    ))

    # Starting point: Union Square at 9:00 AM (0 minutes)
    # Only one meeting can be first, and it must account for travel from Union Square
    first_meeting_constraints = []
    for friend in friends:
        travel_time = travel_times.get(("Union Square", friend['location']), 0)
        if travel_time > 0:
            first_meeting_constraints.append(
                And(friend['met'], meeting_order[friends.index(friend)] == 0,
                    friend['start_var'] >= travel_time)
            )
    opt.add(Or(first_meeting_constraints))

    # Maximize number of friends met
    opt.maximize(Sum([If(friend['met'], 1, 0) for friend in friends]))

    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for friend in friends:
            if model.eval(friend['met']):
                start = model.eval(friend['start_var']).as_long()
                end = model.eval(friend['end_var']).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": friend['name'],
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end),
                    "location": friend['location']
                })
        # Sort by actual meeting time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling()
print(json.dumps(solution, indent=2))