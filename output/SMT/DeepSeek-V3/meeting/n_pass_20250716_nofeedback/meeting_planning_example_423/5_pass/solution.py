from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define travel times (in minutes) between locations
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

    # Friends' availability and meeting constraints
    friends = {
        'Jason': {
            'location': 'Richmond District',
            'available_start': 13 * 60,  # 1:00 PM in minutes
            'available_end': 20 * 60 + 45,  # 8:45 PM in minutes
            'min_duration': 90,
        },
        'Melissa': {
            'location': 'North Beach',
            'available_start': 18 * 60 + 45,  # 6:45 PM in minutes
            'available_end': 20 * 60 + 15,  # 8:15 PM in minutes
            'min_duration': 45,
        },
        'Brian': {
            'location': 'Financial District',
            'available_start': 9 * 60 + 45,  # 9:45 AM in minutes
            'available_end': 21 * 60 + 45,  # 9:45 PM in minutes
            'min_duration': 15,
        },
        'Elizabeth': {
            'location': 'Golden Gate Park',
            'available_start': 8 * 60 + 45,  # 8:45 AM in minutes
            'available_end': 21 * 60 + 30,  # 9:30 PM in minutes
            'min_duration': 105,
        },
        'Laura': {
            'location': 'Union Square',
            'available_start': 14 * 60 + 15,  # 2:15 PM in minutes
            'available_end': 19 * 60 + 30,  # 7:30 PM in minutes
            'min_duration': 75,
        }
    }

    # Current location starts at Presidio at 9:00 AM (540 minutes)
    current_time = 9 * 60
    current_location = 'Presidio'

    # Define variables for each meeting's start and end times
    meeting_vars = {}
    for friend in friends:
        meeting_vars[friend] = {
            'start': Int(f'start_{friend}'),
            'end': Int(f'end_{friend}'),
            'met': Bool(f'met_{friend}'),
            'location': friends[friend]['location'],
        }

    # Constraints for each friend
    for friend in friends:
        data = friends[friend]
        start = meeting_vars[friend]['start']
        end = meeting_vars[friend]['end']
        met = meeting_vars[friend]['met']

        # If meeting the friend, enforce time constraints
        opt.add(Implies(met, start >= data['available_start']))
        opt.add(Implies(met, end <= data['available_end']))
        opt.add(Implies(met, end - start >= data['min_duration']))
        opt.add(Implies(Not(met), start == -1))
        opt.add(Implies(Not(met), end == -1))

    # Define sequencing constraints to account for travel times
    # We'll create a list of all possible meeting pairs and ensure proper sequencing
    friend_list = list(friends.keys())
    for i in range(len(friend_list)):
        for j in range(i+1, len(friend_list)):
            f1 = friend_list[i]
            f2 = friend_list[j]
            # Either f1 is before f2 or vice versa
            # If both are met, ensure proper travel time between them
            opt.add(Implies(And(meeting_vars[f1]['met'], meeting_vars[f2]['met']),
                Or(
                    meeting_vars[f1]['end'] + travel_times[(meeting_vars[f1]['location'], meeting_vars[f2]['location'])] <= meeting_vars[f2]['start'],
                    meeting_vars[f2]['end'] + travel_times[(meeting_vars[f2]['location'], meeting_vars[f1]['location'])] <= meeting_vars[f1]['start']
                )
            ))

    # Maximize the number of friends met
    opt.maximize(Sum([If(meeting_vars[friend]['met'], 1, 0) for friend in friends]))

    # Check if a solution exists
    if opt.check() == sat:
        m = opt.model()
        itinerary = []

        # Collect all meetings that were met
        met_meetings = []
        for friend in friends:
            if m.evaluate(meeting_vars[friend]['met']):
                start = m.evaluate(meeting_vars[friend]['start']).as_long()
                end = m.evaluate(meeting_vars[friend]['end']).as_long()
                location = meeting_vars[friend]['location']
                met_meetings.append({
                    'person': friend,
                    'start': start,
                    'end': end,
                    'location': location,
                })

        # Sort meetings by start time
        met_meetings.sort(key=lambda x: x['start'])

        # Verify travel times between consecutive meetings
        valid = True
        for i in range(len(met_meetings) - 1):
            current = met_meetings[i]
            next_meeting = met_meetings[i + 1]
            travel_time = travel_times.get((current['location'], next_meeting['location']), 0)
            if current['end'] + travel_time > next_meeting['start']:
                valid = False
                break

        if valid:
            for meeting in met_meetings:
                start_time = f"{meeting['start'] // 60:02d}:{meeting['start'] % 60:02d}"
                end_time = f"{meeting['end'] // 60:02d}:{meeting['end'] % 60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": meeting['person'],
                    "start_time": start_time,
                    "end_time": end_time
                })
            return {"itinerary": itinerary}
        else:
            return {"itinerary": []}
    else:
        return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))