from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver with optimization
    s = Optimize()

    # Define the friends and their details
    friends = [
        {"name": "Joshua", "location": "Embarcadero", "available_start": "9:45", "available_end": "18:00", "duration": 105},
        {"name": "Jeffrey", "location": "Bayview", "available_start": "9:45", "available_end": "20:15", "duration": 75},
        {"name": "Charles", "location": "Union Square", "available_start": "10:45", "available_end": "20:15", "duration": 120},
        {"name": "Joseph", "location": "Chinatown", "available_start": "7:00", "available_end": "15:30", "duration": 60},
        {"name": "Elizabeth", "location": "Sunset District", "available_start": "9:00", "available_end": "9:45", "duration": 45},
        {"name": "Matthew", "location": "Golden Gate Park", "available_start": "11:00", "available_end": "19:30", "duration": 45},
        {"name": "Carol", "location": "Financial District", "available_start": "10:45", "available_end": "11:15", "duration": 15},
        {"name": "Paul", "location": "Haight-Ashbury", "available_start": "19:15", "available_end": "20:30", "duration": 15},
        {"name": "Rebecca", "location": "Mission District", "available_start": "17:00", "available_end": "21:45", "duration": 45}
    ]

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Travel times dictionary (from_location, to_location) -> minutes
    travel_times = {
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Mission District"): 20,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Bayview"): 21,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Mission District"): 20,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Embarcadero"): 19,
        ("Bayview", "Union Square"): 18,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Sunset District"): 23,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Mission District"): 13,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Mission District"): 14,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Bayview"): 20,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Mission District"): 17,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Mission District"): 25,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Mission District"): 17,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Mission District"): 17,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "Embarcadero"): 19,
        ("Mission District", "Bayview"): 14,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Financial District"): 15,
        ("Mission District", "Haight-Ashbury"): 12
    }

    # Create variables for each meeting
    meetings = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        duration = friend['duration']
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        meetings.append({
            "name": friend['name'],
            "location": friend['location'],
            "start": start,
            "end": end,
            "duration": duration,
            "available_start": available_start,
            "available_end": available_end
        })

    # Basic constraints for each meeting
    for meeting in meetings:
        s.add(meeting['start'] >= meeting['available_start'])
        s.add(meeting['end'] <= meeting['available_end'])
        s.add(meeting['end'] == meeting['start'] + meeting['duration'])

    # Starting point
    current_location = "Marina District"
    current_time = time_to_minutes("9:00")  # 9:00 AM

    # We'll meet Elizabeth first since she's only available until 9:45
    elizabeth = next(m for m in meetings if m['name'] == 'Elizabeth')
    s.add(elizabeth['start'] == current_time)
    current_time = elizabeth['end']
    current_location = elizabeth['location']

    # Create variables for the order of remaining meetings
    remaining_meetings = [m for m in meetings if m['name'] != 'Elizabeth']
    n = len(remaining_meetings)
    order = [Int(f'order_{i}') for i in range(n)]
    s.add(Distinct(order))
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)

    # Variables for the current time and location at each step
    step_time = [Int(f'step_time_{i}') for i in range(n+1)]
    step_location = [String(f'step_location_{i}') for i in range(n+1)]
    s.add(step_time[0] == current_time)
    s.add(step_location[0] == current_location)

    # Constraints for each step
    for i in range(n):
        meeting_idx = order[i]
        meeting = remaining_meetings[meeting_idx]
        
        # Travel time from previous location to meeting location
        travel_time = Int(f'travel_{i}')
        from_loc = step_location[i]
        to_loc = meeting['location']
        s.add(travel_time == travel_times[(from_loc, to_loc)])
        
        # Meeting must start after arrival
        s.add(meeting['start'] >= step_time[i] + travel_time)
        
        # Update step time and location
        s.add(step_time[i+1] == meeting['end'])
        s.add(step_location[i+1] == to_loc)

    # Maximize the number of meetings (soft constraints)
    met = [Bool(f'met_{m["name"]}') for m in remaining_meetings]
    for i, m in enumerate(remaining_meetings):
        s.add(Implies(met[i], m['start'] >= 0))  # If met, start time must be valid
    s.maximize(Sum([If(m, 1, 0) for m in met]))

    # Solve
    if s.check() == sat:
        model = s.model()
        itinerary = [{
            "action": "meet",
            "person": "Elizabeth",
            "start_time": minutes_to_time(model.evaluate(elizabeth['start']).as_long()),
            "end_time": minutes_to_time(model.evaluate(elizabeth['end']).as_long())
        }]
        
        # Get the order of remaining meetings
        meeting_order = []
        for i in range(n):
            idx = model.evaluate(order[i]).as_long()
            meeting_order.append(remaining_meetings[idx])
        
        # Add them to itinerary in order
        current_time = model.evaluate(elizabeth['end']).as_long()
        current_location = "Sunset District"
        for meeting in meeting_order:
            if model.evaluate(met[remaining_meetings.index(meeting)]):
                itinerary.append({
                    "action": "meet",
                    "person": meeting['name'],
                    "start_time": minutes_to_time(model.evaluate(meeting['start']).as_long()),
                    "end_time": minutes_to_time(model.evaluate(meeting['end']).as_long())
                })
        
        # Sort by start time (should already be ordered)
        itinerary.sort(key=lambda x: time_to_minutes(x['start_time']))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print
solution = solve_scheduling()
print("SOLUTION:")
print(json.dumps(solution, indent=2))