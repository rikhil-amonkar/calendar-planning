from z3 import *
import json

def solve_scheduling_problem():
    s = Solver()

    # Define friends and their availability
    friends = {
        "Elizabeth": {"location": "Financial District", "start": "10:00", "end": "12:45", "min_duration": 75},
        "Joseph": {"location": "Union Square", "start": "11:45", "end": "14:45", "min_duration": 120},
        "Ashley": {"location": "Russian Hill", "start": "11:30", "end": "21:30", "min_duration": 45},
        "Karen": {"location": "Mission District", "start": "14:15", "end": "22:00", "min_duration": 30},
        "Richard": {"location": "Fisherman's Wharf", "start": "14:30", "end": "17:30", "min_duration": 30},
        "Kimberly": {"location": "Haight-Ashbury", "start": "14:15", "end": "17:30", "min_duration": 105},
        "Helen": {"location": "Sunset District", "start": "14:45", "end": "20:45", "min_duration": 105},
        "Robert": {"location": "Presidio", "start": "21:45", "end": "22:45", "min_duration": 60}
    }

    # Convert time to minutes since 9:00 AM (540 minutes since midnight)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540

    def minutes_to_time(minutes):
        total = minutes + 540
        hh = total // 60
        mm = total % 60
        return f"{hh:02d}:{mm:02d}"

    # Create variables for each meeting
    variables = {}
    for name in friends:
        variables[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'met': Bool(f'met_{name}')  # Whether we meet this friend
        }

    # Travel times between locations
    travel_times = {
        ("Financial District", "Union Square"): 9,
        ("Union Square", "Russian Hill"): 13,
        ("Russian Hill", "Mission District"): 16,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Sunset District", "Presidio"): 16,
        # Add other necessary travel times
        ("Financial District", "Russian Hill"): 11,
        ("Russian Hill", "Union Square"): 10,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Presidio", "Sunset District"): 15
    }

    # Base constraints for each friend
    for name in friends:
        friend = friends[name]
        start_time = time_to_minutes(friend['start'])
        end_time = time_to_minutes(friend['end'])
        min_duration = friend['min_duration']

        # If we meet this friend, enforce time constraints
        s.add(Implies(variables[name]['met'],
                      And(variables[name]['start'] >= start_time,
                          variables[name]['end'] <= end_time,
                          variables[name]['end'] - variables[name]['start'] >= min_duration)))

    # Meeting sequence constraints
    # We'll try a reasonable sequence that might work
    sequence = ["Elizabeth", "Joseph", "Ashley", "Karen", "Richard", "Kimberly", "Helen", "Robert"]
    
    # Ensure we meet all friends (change this if not all can be met)
    for name in friends:
        s.add(variables[name]['met'] == True)

    # Add travel time constraints between consecutive meetings
    for i in range(len(sequence)-1):
        current = sequence[i]
        next_p = sequence[i+1]
        current_loc = friends[current]['location']
        next_loc = friends[next_p]['location']
        travel = travel_times.get((current_loc, next_loc), 60)  # Default to 60 if not found
        
        s.add(Implies(And(variables[current]['met'], variables[next_p]['met']),
              variables[next_p]['start'] >= variables[current]['end'] + travel))

    # Ensure first meeting starts after 9:00 AM
    s.add(variables[sequence[0]]['start'] >= 0)

    # Try to solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for name in sequence:
            if is_true(m.evaluate(variables[name]['met'])):
                start = m.evaluate(variables[name]['start']).as_long()
                end = m.evaluate(variables[name]['end']).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
        return {"itinerary": itinerary}
    else:
        # If initial sequence fails, try alternative sequences
        # This is a simplified approach - a full solution would explore all permutations
        alternative_sequences = [
            ["Elizabeth", "Ashley", "Joseph", "Karen", "Richard", "Kimberly", "Helen", "Robert"],
            ["Elizabeth", "Joseph", "Ashley", "Kimberly", "Helen", "Karen", "Richard", "Robert"]
        ]
        
        for seq in alternative_sequences:
            s.reset()
            # Re-add all constraints
            for name in friends:
                friend = friends[name]
                start_time = time_to_minutes(friend['start'])
                end_time = time_to_minutes(friend['end'])
                min_duration = friend['min_duration']
                s.add(Implies(variables[name]['met'],
                            And(variables[name]['start'] >= start_time,
                                variables[name]['end'] <= end_time,
                                variables[name]['end'] - variables[name]['start'] >= min_duration)))
            
            for name in friends:
                s.add(variables[name]['met'] == True)
            
            for i in range(len(seq)-1):
                current = seq[i]
                next_p = seq[i+1]
                current_loc = friends[current]['location']
                next_loc = friends[next_p]['location']
                travel = travel_times.get((current_loc, next_loc), 60)
                s.add(Implies(And(variables[current]['met'], variables[next_p]['met']),
                            variables[next_p]['start'] >= variables[current]['end'] + travel))
            
            s.add(variables[seq[0]]['start'] >= 0)
            
            if s.check() == sat:
                m = s.model()
                itinerary = []
                for name in seq:
                    if is_true(m.evaluate(variables[name]['met'])):
                        start = m.evaluate(variables[name]['start']).as_long()
                        end = m.evaluate(variables[name]['end']).as_long()
                        itinerary.append({
                            "action": "meet",
                            "person": name,
                            "start_time": minutes_to_time(start),
                            "end_time": minutes_to_time(end)
                        })
                return {"itinerary": itinerary}
        
        return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))