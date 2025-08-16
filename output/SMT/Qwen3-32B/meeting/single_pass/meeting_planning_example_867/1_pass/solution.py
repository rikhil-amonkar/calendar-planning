import itertools
from z3 import Solver, Int, And, Distinct, sat, Implies
import json
import sys

friends = [
    {
        'name': 'Elizabeth',
        'location': 'Mission District',
        'start_window': 630,
        'end_window': 1200,
        'duration': 90
    },
    {
        'name': 'David',
        'location': 'Union Square',
        'start_window': 915,
        'end_window': 1140,
        'duration': 45
    },
    {
        'name': 'Sandra',
        'location': 'Pacific Heights',
        'start_window': 420,
        'end_window': 1200,
        'duration': 120
    },
    {
        'name': 'Thomas',
        'location': 'Bayview',
        'start_window': 1170,
        'end_window': 1230,
        'duration': 30
    },
    {
        'name': 'Robert',
        'location': 'Fisherman\'s Wharf',
        'start_window': 600,
        'end_window': 900,
        'duration': 15
    },
    {
        'name': 'Kenneth',
        'location': 'Marina District',
        'start_window': 645,
        'end_window': 780,
        'duration': 45
    },
    {
        'name': 'Melissa',
        'location': 'Richmond District',
        'start_window': 1095,
        'end_window': 1200,
        'duration': 15
    },
    {
        'name': 'Kimberly',
        'location': 'Sunset District',
        'start_window': 615,
        'end_window': 1095,
        'duration': 105
    },
    {
        'name': 'Amanda',
        'location': 'Golden Gate Park',
        'start_window': 465,
        'end_window': 1125,
        'duration': 15
    }
]

travel_times = {
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Bayview'): 14,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Bayview'): 27,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 25,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Sunset District'): 10,
}

def is_subset_feasible(subset):
    n = len(subset)
    if n == 0:
        return None
    s = Solver()
    pos_vars = {}
    for friend in subset:
        pos_vars[friend['name']] = Int('pos_%s' % friend['name'])
    # Constraints: positions are distinct and between 0 and n-1
    for friend in subset:
        s.add(And(pos_vars[friend['name']] >= 0, pos_vars[friend['name']] < n))
    s.add(Distinct([pos_vars[friend['name']] for friend in subset]))
    # Variables for start and end times
    start_vars = {}
    end_vars = {}
    for friend in subset:
        start_vars[friend['name']] = Int('start_%s' % friend['name'])
        end_vars[friend['name']] = Int('end_%s' % friend['name'])
        # end = start + duration
        s.add(end_vars[friend['name']] == start_vars[friend['name']] + friend['duration'])
        # start >= start_window
        s.add(start_vars[friend['name']] >= friend['start_window'])
        # end <= end_window
        s.add(end_vars[friend['name']] <= friend['end_window'])
    # Constraint for first in sequence (pos == 0)
    for friend in subset:
        loc = friend['location']
        travel_time = travel_times[('Haight-Ashbury', loc)]
        s.add(Implies(pos_vars[friend['name']] == 0,
                      start_vars[friend['name']] >= 540 + travel_time))
    # Constraints for consecutive positions
    for x in subset:
        for y in subset:
            if x == y:
                continue
            x_pos = pos_vars[x['name']]
            y_pos = pos_vars[y['name']]
            # If x is immediately before y in the sequence
            cond = (x_pos + 1 == y_pos)
            travel_time = travel_times[(x['location'], y['location'])]
            constraint = start_vars[y['name']] >= end_vars[x['name']] + travel_time
            s.add(Implies(cond, constraint))
    # Check satisfiability
    if s.check() == sat:
        model = s.model()
        # Extract the order and times
        order = []
        for friend in subset:
            pos_val = model[pos_vars[friend['name']]]
            order.append( (pos_val.as_long(), friend) )
        # Sort by position
        order.sort()
        # Build the itinerary
        itinerary = []
        for pos, friend in order:
            start_time = model[start_vars[friend['name']]].as_long()
            end_time = model[end_vars[friend['name']]].as_long()
            # Convert to HH:MM
            start_h = start_time // 60
            start_m = start_time % 60
            end_h = end_time // 60
            end_m = end_time % 60
            itinerary.append({
                'action': 'meet',
                'person': friend['name'],
                'start_time': f"{start_h:02d}:{start_m:02d}",
                'end_time': f"{end_h:02d}:{end_m:02d}"
            })
        return {'itinerary': itinerary}
    else:
        return None

# Main loop to find the best subset
for size in range(len(friends), 0, -1):
    for subset in itertools.combinations(friends, size):
        result = is_subset_feasible(subset)
        if result is not None:
            print(json.dumps(result))
            sys.exit(0)

print(json.dumps({"itinerary": []}))