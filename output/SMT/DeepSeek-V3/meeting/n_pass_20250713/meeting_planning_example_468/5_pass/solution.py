from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()
    
    # Friends and their locations with priority based on time window tightness
    friends = [
        {'name': 'Rebecca', 'location': 'Bayview', 'window': (0, 225), 'duration': 90},
        {'name': 'Amanda', 'location': 'Pacific Heights', 'window': (570, 645), 'duration': 90},
        {'name': 'James', 'location': 'Alamo Square', 'window': (45, 735), 'duration': 90},
        {'name': 'Sarah', 'location': 'Fisherman\'s Wharf', 'window': (-60, 750), 'duration': 90},
        {'name': 'Melissa', 'location': 'Golden Gate Park', 'window': (0, 585), 'duration': 90}
    ]
    
    # Travel times (in minutes)
    travel_times = {
        ('The Castro', 'Bayview'): 19,
        ('The Castro', 'Pacific Heights'): 16,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Fisherman\'s Wharf'): 24,
        ('The Castro', 'Golden Gate Park'): 11,
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Golden Gate Park'): 22,
        ('Pacific Heights', 'Alamo Square'): 10,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25
    }
    
    # Create variables for each meeting
    meetings = []
    for friend in friends:
        start = Int(f'start_{friend["name"]}')
        end = Int(f'end_{friend["name"]}')
        met = Bool(f'met_{friend["name"]}')
        meetings.append({
            'name': friend['name'],
            'location': friend['location'],
            'start': start,
            'end': end,
            'met': met,
            'window': friend['window'],
            'duration': friend['duration']
        })
    
    # Constraints for each meeting
    for m in meetings:
        s.add(Implies(m['met'], m['start'] >= m['window'][0]))
        s.add(Implies(m['met'], m['end'] <= m['window'][1]))
        s.add(Implies(m['met'], m['end'] == m['start'] + m['duration']))
        s.add(Implies(Not(m['met']), m['start'] == -1))
        s.add(Implies(Not(m['met']), m['end'] == -1))
    
    # No overlap constraints considering travel times
    for i in range(len(meetings)):
        for j in range(i+1, len(meetings)):
            m1 = meetings[i]
            m2 = meetings[j]
            loc1 = m1['location']
            loc2 = m2['location']
            travel = travel_times.get((loc1, loc2), travel_times.get((loc2, loc1), 0))
            s.add(Implies(And(m1['met'], m2['met']),
                          Or(m1['end'] + travel <= m2['start'],
                             m2['end'] + travel <= m1['start'])))
    
    # Must meet all 5 people
    s.add(And([m['met'] for m in meetings]))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        scheduled = []
        for meeting in meetings:
            if m.evaluate(meeting['met']):
                start = m.evaluate(meeting['start']).as_long()
                end = m.evaluate(meeting['end']).as_long()
                scheduled.append({
                    'name': meeting['name'],
                    'location': meeting['location'],
                    'start': start,
                    'end': end
                })
        
        # Sort by start time
        scheduled.sort(key=lambda x: x['start'])
        
        # Print schedule
        print("Optimal Schedule:")
        for meet in scheduled:
            start_time = (9 * 60 + meet['start']) % (24 * 60)
            end_time = (9 * 60 + meet['end']) % (24 * 60)
            start_h, start_m = divmod(start_time, 60)
            end_h, end_m = divmod(end_time, 60)
            print(f"Meet {meet['name']} at {meet['location']} from {start_h:02d}:{start_m:02d} to {end_h:02d}:{end_m:02d}")
        print(f"Total friends met: {len(scheduled)}")
    else:
        print("No feasible schedule found that meets all 5 friends.")

solve_scheduling()