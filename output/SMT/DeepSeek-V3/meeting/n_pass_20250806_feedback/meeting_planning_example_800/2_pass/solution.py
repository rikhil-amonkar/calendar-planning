from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Friends and their details
    friends = {
        "Melissa": {"location": "The Castro", "start": "20:15", "end": "21:15", "min_duration": 30},
        "Kimberly": {"location": "North Beach", "start": "07:00", "end": "10:30", "min_duration": 15},
        "Joseph": {"location": "Embarcadero", "start": "15:30", "end": "19:30", "min_duration": 75},
        "Barbara": {"location": "Alamo Square", "start": "20:45", "end": "21:45", "min_duration": 15},
        "Kenneth": {"location": "Nob Hill", "start": "12:15", "end": "17:15", "min_duration": 105},
        "Joshua": {"location": "Presidio", "start": "16:30", "end": "18:15", "min_duration": 105},
        "Brian": {"location": "Fisherman's Wharf", "start": "09:30", "end": "15:30", "min_duration": 45},
        "Steven": {"location": "Mission District", "start": "19:30", "end": "21:00", "min_duration": 90},
        "Betty": {"location": "Haight-Ashbury", "start": "19:00", "end": "20:30", "min_duration": 90}
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes, since 9*60=540)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Initialize variables for each friend's meeting start and end times (in minutes since 9:00 AM)
    variables = {}
    for name in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        variables[name] = {'start': start_var, 'end': end_var}

    # Add constraints for each friend
    for name in friends:
        friend = friends[name]
        start_time = time_to_minutes(friend['start'])
        end_time = time_to_minutes(friend['end'])
        min_duration = friend['min_duration']
        s.add(variables[name]['start'] >= start_time - 540)  # Relative to 9:00 AM (540)
        s.add(variables[name]['end'] <= end_time - 540)
        s.add(variables[name]['end'] - variables[name]['start'] >= min_duration)

    # Define travel times between locations (in minutes)
    travel_times = {
        ("Union Square", "The Castro"): 17,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Haight-Ashbury"): 18,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Haight-Ashbury"): 6,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "The Castro"): 23,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Mission District"): 18,
        ("North Beach", "Haight-Ashbury"): 18,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Mission District"): 20,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Embarcadero"): 19,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Mission District"): 11
    }

    # Define the order of meetings (this is a heuristic; in practice, we'd need to explore permutations)
    # For simplicity, we'll assume a possible order and check feasibility
    meeting_order = ["Kimberly", "Brian", "Kenneth", "Joseph", "Joshua", "Betty", "Steven", "Melissa", "Barbara"]

    # Add constraints for travel times between meetings
    for i in range(len(meeting_order) - 1):
        current = meeting_order[i]
        next_p = meeting_order[i + 1]
        current_loc = friends[current]['location']
        next_loc = friends[next_p]['location']
        travel_time = travel_times.get((current_loc, next_loc), 0)
        s.add(variables[next_p]['start'] >= variables[current]['end'] + travel_time)

    # Also ensure that the first meeting starts after travel from Union Square
    first_meeting = meeting_order[0]
    first_loc = friends[first_meeting]['location']
    travel_time_first = travel_times.get(("Union Square", first_loc), 0)
    s.add(variables[first_meeting]['start'] >= travel_time_first)

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in meeting_order:
            start = model.evaluate(variables[name]['start']).as_long() + 540
            end = model.evaluate(variables[name]['end']).as_long() + 540
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        return {"itinerary": itinerary}
    else:
        # If the initial order doesn't work, try a different order
        # For simplicity, we'll try a different order here
        meeting_order = ["Kimberly", "Brian", "Kenneth", "Joshua", "Joseph", "Betty", "Steven", "Melissa", "Barbara"]
        s.reset()
        for name in friends:
            friend = friends[name]
            start_time = time_to_minutes(friend['start'])
            end_time = time_to_minutes(friend['end'])
            min_duration = friend['min_duration']
            s.add(variables[name]['start'] >= start_time - 540)
            s.add(variables[name]['end'] <= end_time - 540)
            s.add(variables[name]['end'] - variables[name]['start'] >= min_duration)
        for i in range(len(meeting_order) - 1):
            current = meeting_order[i]
            next_p = meeting_order[i + 1]
            current_loc = friends[current]['location']
            next_loc = friends[next_p]['location']
            travel_time = travel_times.get((current_loc, next_loc), 0)
            s.add(variables[next_p]['start'] >= variables[current]['end'] + travel_time)
        first_meeting = meeting_order[0]
        first_loc = friends[first_meeting]['location']
        travel_time_first = travel_times.get(("Union Square", first_loc), 0)
        s.add(variables[first_meeting]['start'] >= travel_time_first)
        if s.check() == sat:
            model = s.model()
            itinerary = []
            for name in meeting_order:
                start = model.evaluate(variables[name]['start']).as_long() + 540
                end = model.evaluate(variables[name]['end']).as_long() + 540
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
            return {"itinerary": itinerary}
        else:
            return {"itinerary": []}

# Execute the solver
result = solve_scheduling()
print(json.dumps(result, indent=2))