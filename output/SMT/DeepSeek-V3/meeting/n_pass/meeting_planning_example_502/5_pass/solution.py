from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    solver = Solver()

    # Define locations and their indices
    locations = {
        'Financial District': 0,
        'Golden Gate Park': 1,
        'Chinatown': 2,
        'Union Square': 3,
        'Fisherman\'s Wharf': 4,
        'Pacific Heights': 5,
        'North Beach': 6
    }

    # Travel times between locations (in minutes)
    travel_times = {
        (0,1):23, (0,2):5, (0,3):9, (0,4):10, (0,5):13, (0,6):7,
        (1,0):26, (1,2):23, (1,3):22, (1,4):24, (1,5):16, (1,6):24,
        (2,0):5, (2,1):23, (2,3):7, (2,4):8, (2,5):10, (2,6):3,
        (3,0):9, (3,1):22, (3,2):7, (3,4):15, (3,5):15, (3,6):10,
        (4,0):11, (4,1):25, (4,2):12, (4,3):13, (4,5):12, (4,6):6,
        (5,0):13, (5,1):15, (5,2):11, (5,3):12, (5,4):13, (5,6):9,
        (6,0):8, (6,1):22, (6,2):6, (6,3):7, (6,4):5, (6,5):8
    }

    # Friends' availability
    friends = [
        {'name': 'Joseph', 'location': 'Pacific Heights', 'start': 495, 'end': 570, 'min_duration': 60},
        {'name': 'Rebecca', 'location': 'Fisherman\'s Wharf', 'start': 480, 'end': 675, 'min_duration': 30},
        {'name': 'Stephanie', 'location': 'Golden Gate Park', 'start': 660, 'end': 900, 'min_duration': 105},
        {'name': 'Karen', 'location': 'Chinatown', 'start': 825, 'end': 990, 'min_duration': 15},
        {'name': 'Steven', 'location': 'North Beach', 'start': 870, 'end': 1245, 'min_duration': 120},
        {'name': 'Brian', 'location': 'Union Square', 'start': 900, 'end': 1035, 'min_duration': 30}
    ]

    # Current location and time (Financial District at 9:00 AM = 540 minutes)
    current_loc = locations['Financial District']
    current_time = 540

    # Create meeting variables
    meetings = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        duration = Int(f"dur_{friend['name']}")
        loc = locations[friend['location']]
        
        meetings.append({
            'name': friend['name'],
            'start': start,
            'end': end,
            'duration': duration,
            'location': loc,
            'info': friend
        })

    # Basic meeting constraints
    for m in meetings:
        solver.add(m['start'] >= m['info']['start'])
        solver.add(m['end'] <= m['info']['end'])
        solver.add(m['duration'] >= m['info']['min_duration'])
        solver.add(m['end'] == m['start'] + m['duration'])

    # Determine meeting order
    order = [Int(f"order_{i}") for i in range(len(meetings))]
    solver.add(Distinct(order))
    for i in range(len(meetings)):
        solver.add(order[i] >= 0)
        solver.add(order[i] < len(meetings))

    # Travel time constraints between consecutive meetings
    for i in range(len(meetings)):
        for j in range(len(meetings)):
            if i != j:
                solver.add(Implies(
                    order[i] < order[j],
                    meetings[j]['start'] >= meetings[i]['end'] + travel_times[(meetings[i]['location'], meetings[j]['location'])]
                ))

    # First meeting must be reachable from starting location
    for i in range(len(meetings)):
        solver.add(Implies(
            order[i] == 0,
            meetings[i]['start'] >= current_time + travel_times[(current_loc, meetings[i]['location'])]
        ))

    # Check if we can meet all friends
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for m in meetings:
            s = model.evaluate(m['start']).as_long()
            e = model.evaluate(m['end']).as_long()
            if e - s >= m['info']['min_duration']:
                itinerary.append({
                    "action": "meet",
                    "person": m['name'],
                    "start_time": f"{s//60:02d}:{s%60:02d}",
                    "end_time": f"{e//60:02d}:{e%60:02d}"
                })
        
        # Sort by start time
        itinerary.sort(key=lambda x: (int(x['start_time'][:2]), int(x['start_time'][3:])))
        return {"itinerary": itinerary}
    else:
        # If can't meet all, try meeting as many as possible
        return try_partial_schedule(meetings, travel_times, current_loc, current_time)

def try_partial_schedule(meetings, travel_times, current_loc, current_time):
    # Try to meet as many friends as possible
    opt = Optimize()
    
    # Binary variables indicating if we meet each friend
    meet_vars = [Int(f"meet_{m['name']}") for m in meetings]
    for v in meet_vars:
        opt.add(Or(v == 0, v == 1))
    
    # Order variables
    order = [Int(f"order_{i}") for i in range(len(meetings))]
    opt.add(Distinct([If(meet_vars[i] == 1, order[i], -1) for i in range(len(meetings))]))
    
    # Meeting constraints for selected friends
    for i, m in enumerate(meetings):
        opt.add(Implies(
            meet_vars[i] == 1,
            And(
                m['start'] >= m['info']['start'],
                m['end'] <= m['info']['end'],
                m['duration'] >= m['info']['min_duration'],
                m['end'] == m['start'] + m['duration']
            )
        ))
    
    # Travel time constraints
    for i in range(len(meetings)):
        for j in range(len(meetings)):
            if i != j:
                opt.add(Implies(
                    And(meet_vars[i] == 1, meet_vars[j] == 1, order[i] < order[j]),
                    meetings[j]['start'] >= meetings[i]['end'] + travel_times[(meetings[i]['location'], meetings[j]['location'])]
                ))
    
    # First meeting constraint
    for i in range(len(meetings)):
        opt.add(Implies(
            And(meet_vars[i] == 1, order[i] == 0),
            meetings[i]['start'] >= current_time + travel_times[(current_loc, meetings[i]['location'])]
        ))
    
    # Maximize number of friends met
    total_met = Int('total_met')
    opt.add(total_met == sum(meet_vars))
    opt.maximize(total_met)
    
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for i, m in enumerate(meetings):
            if model.evaluate(meet_vars[i]).as_long() == 1:
                s = model.evaluate(m['start']).as_long()
                e = model.evaluate(m['end']).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": m['name'],
                    "start_time": f"{s//60:02d}:{s%60:02d}",
                    "end_time": f"{e//60:02d}:{e%60:02d}"
                })
        
        itinerary.sort(key=lambda x: (int(x['start_time'][:2]), int(x['start_time'][3:])))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))