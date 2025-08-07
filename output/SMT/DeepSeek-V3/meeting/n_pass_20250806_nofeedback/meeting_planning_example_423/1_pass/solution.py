from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define travel times between locations (in minutes)
    travel_times = {
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Financial District'): 23,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Union Square'): 22,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Richmond District', 'Union Square'): 21,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Richmond District'): 18,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Union Square'): 7,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Union Square'): 9,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Richmond District'): 20,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Golden Gate Park'): 22,
    }

    # Define friends' availability and meeting duration requirements
    friends = {
        'Jason': {
            'location': 'Richmond District',
            'start': 13 * 60,  # 1:00 PM in minutes
            'end': 20 * 60 + 45,  # 8:45 PM in minutes
            'duration': 90,  # 90 minutes
        },
        'Melissa': {
            'location': 'North Beach',
            'start': 18 * 60 + 45,  # 6:45 PM in minutes
            'end': 20 * 60 + 15,  # 8:15 PM in minutes
            'duration': 45,  # 45 minutes
        },
        'Brian': {
            'location': 'Financial District',
            'start': 9 * 60 + 45,  # 9:45 AM in minutes
            'end': 21 * 60 + 45,  # 9:45 PM in minutes
            'duration': 15,  # 15 minutes
        },
        'Elizabeth': {
            'location': 'Golden Gate Park',
            'start': 8 * 60 + 45,  # 8:45 AM in minutes
            'end': 21 * 60 + 30,  # 9:30 PM in minutes
            'duration': 105,  # 105 minutes
        },
        'Laura': {
            'location': 'Union Square',
            'start': 14 * 60 + 15,  # 2:15 PM in minutes
            'end': 19 * 60 + 30,  # 7:30 PM in minutes
            'duration': 75,  # 75 minutes
        }
    }

    # Current location starts at Presidio at 9:00 AM (540 minutes)
    current_location = 'Presidio'
    current_time = 9 * 60  # 9:00 AM in minutes

    # Create Z3 variables for each meeting's start and end times
    meeting_vars = {}
    for friend in friends:
        meeting_vars[friend] = {
            'start': Int(f'start_{friend}'),
            'end': Int(f'end_{friend}'),
            'location': friends[friend]['location']
        }

    # Add constraints for each meeting
    for friend in friends:
        info = friends[friend]
        start = meeting_vars[friend]['start']
        end = meeting_vars[friend]['end']
        s.add(start >= info['start'])
        s.add(end <= info['end'])
        s.add(end == start + info['duration'])

    # Define the order of meetings and travel times
    # We'll try to meet all friends, so we need to sequence the meetings
    # and ensure travel times are accounted for between meetings
    all_friends = list(friends.keys())
    for i in range(len(all_friends)):
        for j in range(len(all_friends)):
            if i != j:
                friend1 = all_friends[i]
                friend2 = all_friends[j]
                loc1 = meeting_vars[friend1]['location']
                loc2 = meeting_vars[friend2]['location']
                travel = travel_times.get((loc1, loc2), 0)
                s.add(Or(
                    meeting_vars[friend2]['start'] >= meeting_vars[friend1]['end'] + travel,
                    meeting_vars[friend1]['start'] >= meeting_vars[friend2]['end'] + travel_times.get((loc2, loc1), 0)
                ))

    # Ensure the first meeting starts after arriving at Presidio and traveling to the first location
    for friend in friends:
        loc = meeting_vars[friend]['location']
        travel = travel_times.get((current_location, loc), 0)
        s.add(meeting_vars[friend]['start'] >= current_time + travel)

    # Try to meet as many friends as possible
    # We'll maximize the number of friends met by checking satisfiability with all friends,
    # then removing one if unsat, etc.
    met_friends = all_friends.copy()
    itinerary = []
    while met_friends:
        temp_s = Solver()
        temp_s.add(s.assertions())
        # Add constraint that at least one friend is not met
        for friend in met_friends:
            temp_s.add(meeting_vars[friend]['start'] >= 0)
        if temp_s.check() == sat:
            m = temp_s.model()
            # Extract the meeting times
            for friend in met_friends:
                start = m.evaluate(meeting_vars[friend]['start']).as_long()
                end = m.evaluate(meeting_vars[friend]['end']).as_long()
                itinerary.append({
                    'action': 'meet',
                    'person': friend,
                    'start_time': f"{start // 60:02d}:{start % 60:02d}",
                    'end_time': f"{end // 60:02d}:{end % 60:02d}"
                })
            break
        else:
            met_friends.pop()

    # Sort itinerary by start time
    itinerary.sort(key=lambda x: (int(x['start_time'][:2]), int(x['start_time'][3:5])))

    return {'itinerary': itinerary}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))