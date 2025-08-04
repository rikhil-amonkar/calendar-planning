from z3 import *
import json
from collections import defaultdict

def solve_scheduling():
    s = Solver()

    # Corrected travel times (fixed inconsistencies from previous versions)
    travel_times = {
        ('Marina District', 'Embarcadero'): 14,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Sunset District': 19,
        ('Marina District', 'Golden Gate Park'): 18,
        ('Marina District', 'Financial District'): 17,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Mission District'): 20,
        ('Embarcadero', 'Marina District'): 12,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Union Square'): 10,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Sunset District'): 30,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Financial District'): 5,
        ('Embarcadero', 'Haight-Ashbury'): 21,
        ('Embarcadero', 'Mission District'): 20,
        ('Bayview', 'Marina District'): 27,
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Union Square'): 18,
        ('Bayview', 'Chinatown'): 19,
        ('Bayview', 'Sunset District'): 23,
        ('Bayview', 'Golden Gate Park'): 22,
        ('Bayview', 'Financial District'): 19,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Mission District'): 13,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Embarcadero'): 11,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Sunset District'): 27,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'Mission District'): 14,
        ('Chinatown', 'Marina District'): 12,
        ('Chinatown', 'Embarcadero'): 5,
        ('Chinatown', 'Bayview'): 20,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'Mission District'): 17,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'Embarcadero'): 30,
        ('Sunset District', 'Bayview'): 22,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Financial District'): 30,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Mission District'): 25,
        ('Golden Gate Park', 'Marina District'): 16,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Financial District', 'Marina District'): 15,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Union Square'): 9,
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Sunset District'): 30,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Haight-Ashbury'): 19,
        ('Financial District', 'Mission District'): 17,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Embarcadero'): 20,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Union Square'): 19,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Financial District'): 21,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Mission District', 'Marina District'): 19,
        ('Mission District', 'Embarcadero'): 19,
        ('Mission District', 'Bayview'): 14,
        ('Mission District', 'Union Square'): 15,
        ('Mission District', 'Chinatown'): 16,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Financial District'): 15,
        ('Mission District', 'Haight-Ashbury'): 12,
    }

    # Friends data sorted by priority (tighter windows first)
    friends = [
        {'name': 'Elizabeth', 'location': 'Sunset District', 'start': 9*60, 'end': 9*60+45, 'duration': 45, 'flexible': False},
        {'name': 'Carol', 'location': 'Financial District', 'start': 10*60+45, 'end': 11*60+15, 'duration': 15, 'flexible': False},
        {'name': 'Joseph', 'location': 'Chinatown', 'start': 7*60, 'end': 15*60+30, 'duration': 60, 'flexible': True},
        {'name': 'Matthew', 'location': 'Golden Gate Park', 'start': 11*60, 'end': 19*60+30, 'duration': 45, 'flexible': True},
        {'name': 'Joshua', 'location': 'Embarcadero', 'start': 9*60+45, 'end': 18*60, 'duration': 105, 'flexible': True},
        {'name': 'Charles', 'location': 'Union Square', 'start': 10*60+45, 'end': 20*60+15, 'duration': 120, 'flexible': True},
        {'name': 'Jeffrey', 'location': 'Bayview', 'start': 9*60+45, 'end': 20*60+15, 'duration': 75, 'flexible': True},
        {'name': 'Rebecca', 'location': 'Mission District', 'start': 17*60, 'end': 21*60+45, 'duration': 45, 'flexible': True},
        {'name': 'Paul', 'location': 'Haight-Ashbury', 'start': 19*60+15, 'end': 20*60+30, 'duration': 15, 'flexible': False},
    ]

    # Create variables for each meeting
    meetings = {}
    for friend in friends:
        name = friend['name']
        meetings[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'location': friend['location'],
            'duration': friend['duration'],
            'flexible': friend['flexible']
        }
        s.add(meetings[name]['start'] >= friend['start'])
        s.add(meetings[name]['end'] <= friend['end'])
        s.add(meetings[name]['end'] == meetings[name]['start'] + meetings[name]['duration'])

    # Starting point
    current_time = 9*60  # 9:00 AM
    current_location = 'Marina District'

    # Ensure first meeting is reachable
    for friend in friends:
        loc = friend['location']
        travel = travel_times.get((current_location, loc), 0)
        s.add(meetings[friend['name']]['start'] >= current_time + travel)

    # Add constraints for all pairs of meetings
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            name1 = friends[i]['name']
            name2 = friends[j]['name']
            loc1 = meetings[name1]['location']
            loc2 = meetings[name2]['location']
            travel = travel_times.get((loc1, loc2), 0)
            
            # Either meeting1 before meeting2 or vice versa
            s.add(Or(
                meetings[name1]['end'] + travel <= meetings[name2]['start'],
                meetings[name2]['end'] + travel <= meetings[name1]['start'],
            ))

    # Try to find a solution with original constraints
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for friend in friends:
            name = friend['name']
            start = m[meetings[name]['start']].as_long()
            end = m[meetings[name]['end']].as_long()
            start_time = f"{start//60:02d}:{start%60:02d}"
            end_time = f"{end//60:02d}:{end%60:02d}"
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_time,
                "end_time": end_time,
                "location": friend['location']
            })
        
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary, "note": "Original constraints satisfied"}
    
    # If no solution, try relaxing flexible meetings
    flexible_friends = [f for f in friends if f['flexible']]
    for friend in flexible_friends:
        s.push()
        name = friend['name']
        # Try reducing duration by 15 minutes
        s.add(meetings[name]['end'] <= meetings[name]['start'] + max(friend['duration'] - 15, 15))
        if s.check() == sat:
            m = s.model()
            itinerary = []
            for f in friends:
                n = f['name']
                start = m[meetings[n]['start']].as_long()
                end = m[meetings[n]['end']].as_long()
                start_time = f"{start//60:02d}:{start%60:02d}"
                end_time = f"{end//60:02d}:{end%60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": n,
                    "start_time": start_time,
                    "end_time": end_time,
                    "location": f['location']
                })
            itinerary.sort(key=lambda x: x['start_time'])
            return {"itinerary": itinerary, "note": f"Reduced {name}'s meeting time by 15 minutes"}
        s.pop()

    # If still no solution, try more aggressive relaxation
    for friend in flexible_friends:
        s.push()
        name = friend['name']
        # Try reducing duration by 30 minutes
        s.add(meetings[name]['end'] <= meetings[name]['start'] + max(friend['duration'] - 30, 15))
        if s.check() == sat:
            m = s.model()
            itinerary = []
            for f in friends:
                n = f['name']
                start = m[meetings[n]['start']].as_long()
                end = m[meetings[n]['end']].as_long()
                start_time = f"{start//60:02d}:{start%60:02d}"
                end_time = f"{end//60:02d}:{end%60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": n,
                    "start_time": start_time,
                    "end_time": end_time,
                    "location": f['location']
                })
            itinerary.sort(key=lambda x: x['start_time'])
            return {"itinerary": itinerary, "note": f"Reduced {name}'s meeting time by 30 minutes"}
        s.pop()

    # Final attempt - skip one flexible meeting
    for i, friend_to_skip in enumerate(flexible_friends):
        s.push()
        name_to_skip = friend_to_skip['name']
        # Set duration to 0 (effectively skipping)
        s.add(meetings[name_to_skip]['end'] == meetings[name_to_skip]['start'])
        if s.check() == sat:
            m = s.model()
            itinerary = []
            for f in friends:
                n = f['name']
                start = m[meetings[n]['start']].as_long()
                end = m[meetings[n]['end']].as_long()
                if start == end:  # Skipped meeting
                    continue
                start_time = f"{start//60:02d}:{start%60:02d}"
                end_time = f"{end//60:02d}:{end%60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": n,
                    "start_time": start_time,
                    "end_time": end_time,
                    "location": f['location']
                })
            itinerary.sort(key=lambda x: x['start_time'])
            return {"itinerary": itinerary, "note": f"Skipped meeting with {name_to_skip}"}
        s.pop()

    return {"error": "No feasible schedule found even after relaxing constraints"}

solution = solve_scheduling()
print(json.dumps(solution, indent=2))