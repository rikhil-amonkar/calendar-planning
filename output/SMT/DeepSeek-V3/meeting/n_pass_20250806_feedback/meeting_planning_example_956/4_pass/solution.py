from z3 import *
import json

def solve_scheduling_problem():
    s = Solver()

    # Travel times between locations (minutes)
    travel_times = {
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Richmond District'): 16,
        ('The Castro', 'Financial District'): 21,
        ('The Castro', 'Union Square'): 19,
        ('The Castro', 'Fisherman\'s Wharf'): 24,
        ('The Castro', 'Marina District'): 21,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('The Castro', 'Mission District'): 7,
        ('The Castro', 'Pacific Heights'): 16,
        ('The Castro', 'Golden Gate Park'): 11,
        ('Alamo Square', 'Richmond District'): 11,
        ('Alamo Square', 'Financial District'): 17,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Alamo Square', 'Marina District'): 15,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Alamo Square', 'Mission District'): 10,
        ('Alamo Square', 'Pacific Heights'): 10,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'Union Square'): 21,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Marina District'): 9,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'Mission District'): 20,
        ('Richmond District', 'Pacific Heights'): 10,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Financial District', 'Union Square'): 9,
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Financial District', 'Marina District'): 15,
        ('Financial District', 'Haight-Ashbury'): 19,
        ('Financial District', 'Mission District'): 17,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Union Square', 'Fisherman\'s Wharf'): 15,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'Mission District'): 14,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Fisherman\'s Wharf', 'Marina District'): 9,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Mission District'): 20,
        ('Marina District', 'Pacific Heights'): 7,
        ('Marina District', 'Golden Gate Park'): 18,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Pacific Heights', 'Golden Gate Park'): 15,
    }

    # Friends data with flexible durations
    friends = {
        'William': {'location': 'Alamo Square', 'start': 15*60+15, 'end': 17*60+15, 'min_duration': 60, 'priority': 3},
        'Joshua': {'location': 'Richmond District', 'start': 7*60, 'end': 20*60, 'min_duration': 15, 'priority': 1},
        'Joseph': {'location': 'Financial District', 'start': 11*60+15, 'end': 13*60+30, 'min_duration': 15, 'priority': 2},
        'David': {'location': 'Union Square', 'start': 16*60+45, 'end': 19*60+15, 'min_duration': 45, 'priority': 3},
        'Brian': {'location': 'Fisherman\'s Wharf', 'start': 13*60+45, 'end': 20*60+45, 'min_duration': 105, 'priority': 4},
        'Karen': {'location': 'Marina District', 'start': 11*60+30, 'end': 18*60+30, 'min_duration': 15, 'priority': 1},
        'Anthony': {'location': 'Haight-Ashbury', 'start': 7*60+15, 'end': 10*60+30, 'min_duration': 30, 'priority': 2},
        'Matthew': {'location': 'Mission District', 'start': 17*60+15, 'end': 19*60+15, 'min_duration': 120, 'priority': 4},
        'Helen': {'location': 'Pacific Heights', 'start': 8*60, 'end': 12*60, 'min_duration': 75, 'priority': 3},
        'Jeffrey': {'location': 'Golden Gate Park', 'start': 19*60, 'end': 21*60+30, 'min_duration': 60, 'priority': 3},
    }

    # Create variables
    meeting_vars = {}
    for name in friends:
        friend = friends[name]
        meeting_vars[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'duration': Int(f'duration_{name}'),
            'location': friend['location'],
            'scheduled': Bool(f'scheduled_{name}')
        }

    # Constraints
    for name in friends:
        friend = friends[name]
        var = meeting_vars[name]
        
        # If scheduled, enforce time constraints
        s.add(Implies(var['scheduled'], var['start'] >= friend['start']))
        s.add(Implies(var['scheduled'], var['end'] <= friend['end']))
        s.add(Implies(var['scheduled'], var['end'] == var['start'] + var['duration']))
        s.add(Implies(var['scheduled'], var['duration'] >= friend['min_duration']))
        
        # Allow some flexibility in duration
        s.add(Implies(var['scheduled'], var['duration'] <= friend['min_duration'] + 30))
        
        # Priority constraint (higher priority friends more likely to be scheduled)
        s.add(Implies(var['scheduled'], var['duration'] >= friend['priority'] * 10))

    # Initial conditions
    current_time = 9 * 60  # 9:00 AM
    current_location = 'The Castro'

    # Schedule first meeting
    first_meeting = None
    for name in friends:
        if friends[name]['start'] >= current_time + travel_times[(current_location, friends[name]['location'])]:
            first_meeting = name
            break
    
    if first_meeting:
        s.add(meeting_vars[first_meeting]['scheduled'])
        s.add(meeting_vars[first_meeting]['start'] == current_time + 
             travel_times[(current_location, friends[first_meeting]['location'])])

    # No overlapping meetings
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                s.add(Implies(And(meeting_vars[name1]['scheduled'], meeting_vars[name2]['scheduled']),
                    Or(
                        meeting_vars[name1]['end'] + travel_times[(meeting_vars[name1]['location'], 
                                                                  meeting_vars[name2]['location'])] <= meeting_vars[name2]['start'],
                        meeting_vars[name2]['end'] + travel_times[(meeting_vars[name2]['location'], 
                                                                  meeting_vars[name1]['location'])] <= meeting_vars[name1]['start']
                    )))

    # Maximize number of meetings and total duration
    total_meetings = Sum([If(meeting_vars[name]['scheduled'], 1, 0) for name in friends])
    total_duration = Sum([If(meeting_vars[name]['scheduled'], meeting_vars[name]['duration'], 0) for name in friends])
    
    # Try to maximize both, with priority to number of meetings
    s.maximize(total_meetings * 1000 + total_duration)

    if s.check() == sat:
        m = s.model()
        itinerary = []
        for name in friends:
            if is_true(m[meeting_vars[name]['scheduled']]):
                start = m[meeting_vars[name]['start']].as_long()
                end = m[meeting_vars[name]['end']].as_long()
                start_time = f"{start // 60:02d}:{start % 60:02d}"
                end_time = f"{end // 60:02d}:{end % 60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_time,
                    "end_time": end_time,
                    "location": friends[name]['location']
                })
        
        # Sort by start time
        itinerary.sort(key=lambda x: (int(x['start_time'][:2]), int(x['start_time'][3:])))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))