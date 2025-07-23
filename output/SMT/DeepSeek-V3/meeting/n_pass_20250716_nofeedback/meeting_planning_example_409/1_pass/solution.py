from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define the friends and their availability
    friends = {
        "Thomas": {"location": "Bayview", "start": (15, 30), "end": (18, 30), "min_duration": 120},
        "Stephanie": {"location": "Golden Gate Park", "start": (18, 30), "end": (21, 45), "min_duration": 30},
        "Laura": {"location": "Nob Hill", "start": (8, 45), "end": (16, 15), "min_duration": 30},
        "Betty": {"location": "Marina District", "start": (18, 45), "end": (21, 45), "min_duration": 45},
        "Patricia": {"location": "Embarcadero", "start": (17, 30), "end": (22, 0), "min_duration": 45}
    }

    # Define travel times (from_location, to_location) -> minutes
    travel_times = {
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "Nob Hill"): 20,
        ("Bayview", "Marina District"): 25,
        ("Bayview", "Embarcadero"): 19,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Nob Hill", "Fisherman's Wharf"): 11,
        ("Nob Hill", "Bayview"): 19,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Embarcadero"): 9,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Embarcadero"): 14,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Bayview"): 21,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Marina District"): 12
    }

    # Convert times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m

    current_location = "Fisherman's Wharf"
    current_time = time_to_minutes(9, 0)  # 9:00 AM in minutes

    # Variables for each meeting: start and end times in minutes since 9:00 AM
    meetings = {}
    for name in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        meetings[name] = {'start': start_var, 'end': end_var}

    # Constraints for each meeting
    for name in friends:
        friend = friends[name]
        start_min = time_to_minutes(*friend['start'])
        end_min = time_to_minutes(*friend['end'])
        s.add(meetings[name]['start'] >= start_min)
        s.add(meetings[name]['end'] <= end_min)
        s.add(meetings[name]['end'] - meetings[name]['start'] >= friend['min_duration'])

    # Order of meetings and travel times
    # We need to sequence the meetings considering travel times
    # This is complex, so we'll assume an order and check feasibility
    # Let's try to meet Laura first (since she's available earliest), then Thomas, then Patricia, then Betty or Stephanie

    # Meeting Laura first
    laura_start = meetings['Laura']['start']
    laura_end = meetings['Laura']['end']
    s.add(laura_start >= current_time)
    travel_to_laura = travel_times[(current_location, friends['Laura']['location'])]
    s.add(laura_start >= current_time + travel_to_laura)

    # After Laura, meet Thomas
    thomas_start = meetings['Thomas']['start']
    thomas_end = meetings['Thomas']['end']
    travel_laura_to_thomas = travel_times[(friends['Laura']['location'], friends['Thomas']['location'])]
    s.add(thomas_start >= laura_end + travel_laura_to_thomas)

    # After Thomas, meet Patricia
    patricia_start = meetings['Patricia']['start']
    patricia_end = meetings['Patricia']['end']
    travel_thomas_to_patricia = travel_times[(friends['Thomas']['location'], friends['Patricia']['location'])]
    s.add(patricia_start >= thomas_end + travel_thomas_to_patricia)

    # After Patricia, meet Betty
    betty_start = meetings['Betty']['start']
    betty_end = meetings['Betty']['end']
    travel_patricia_to_betty = travel_times[(friends['Patricia']['location'], friends['Betty']['location'])]
    s.add(betty_start >= patricia_end + travel_patricia_to_betty)

    # After Betty, meet Stephanie
    stephanie_start = meetings['Stephanie']['start']
    stephanie_end = meetings['Stephanie']['end']
    travel_betty_to_stephanie = travel_times[(friends['Betty']['location'], friends['Stephanie']['location'])]
    s.add(stephanie_start >= betty_end + travel_betty_to_stephanie)

    # Check if we can meet all friends
    if s.check() == sat:
        model = s.model()
        itinerary = []

        # Helper function to convert minutes back to HH:MM
        def minutes_to_time(m):
            h = m // 60
            m = m % 60
            return f"{h:02d}:{m:02d}"

        # Add Laura meeting
        laura_s = model.evaluate(meetings['Laura']['start']).as_long()
        laura_e = model.evaluate(meetings['Laura']['end']).as_long()
        itinerary.append({
            "action": "meet",
            "person": "Laura",
            "start_time": minutes_to_time(laura_s),
            "end_time": minutes_to_time(laura_e)
        })

        # Add Thomas meeting
        thomas_s = model.evaluate(meetings['Thomas']['start']).as_long()
        thomas_e = model.evaluate(meetings['Thomas']['end']).as_long()
        itinerary.append({
            "action": "meet",
            "person": "Thomas",
            "start_time": minutes_to_time(thomas_s),
            "end_time": minutes_to_time(thomas_e)
        })

        # Add Patricia meeting
        patricia_s = model.evaluate(meetings['Patricia']['start']).as_long()
        patricia_e = model.evaluate(meetings['Patricia']['end']).as_long()
        itinerary.append({
            "action": "meet",
            "person": "Patricia",
            "start_time": minutes_to_time(patricia_s),
            "end_time": minutes_to_time(patricia_e)
        })

        # Add Betty meeting
        betty_s = model.evaluate(meetings['Betty']['start']).as_long()
        betty_e = model.evaluate(meetings['Betty']['end']).as_long()
        itinerary.append({
            "action": "meet",
            "person": "Betty",
            "start_time": minutes_to_time(betty_s),
            "end_time": minutes_to_time(betty_e)
        })

        # Add Stephanie meeting
        stephanie_s = model.evaluate(meetings['Stephanie']['start']).as_long()
        stephanie_e = model.evaluate(meetings['Stephanie']['end']).as_long()
        itinerary.append({
            "action": "meet",
            "person": "Stephanie",
            "start_time": minutes_to_time(stephanie_s),
            "end_time": minutes_to_time(stephanie_e)
        })

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute the solver
result = solve_scheduling()
print(json.dumps(result, indent=2))