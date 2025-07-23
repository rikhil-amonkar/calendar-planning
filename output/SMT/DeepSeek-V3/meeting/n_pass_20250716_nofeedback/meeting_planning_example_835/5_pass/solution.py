from z3 import *
import json

# Travel times between locations (in minutes)
travel_times = {
    'Pacific Heights': {'Golden Gate Park': 15, 'The Castro': 16, 'Bayview': 22, 'Marina District': 6, 'Union Square': 12, 'Sunset District': 21, 'Alamo Square': 10, 'Financial District': 13, 'Mission District': 15},
    'Golden Gate Park': {'Pacific Heights': 16, 'The Castro': 13, 'Bayview': 23, 'Marina District': 16, 'Union Square': 22, 'Sunset District': 10, 'Alamo Square': 9, 'Financial District': 26, 'Mission District': 17},
    'The Castro': {'Pacific Heights': 16, 'Golden Gate Park': 11, 'Bayview': 19, 'Marina District': 21, 'Union Square': 19, 'Sunset District': 17, 'Alamo Square': 8, 'Financial District': 21, 'Mission District': 7},
    'Bayview': {'Pacific Heights': 23, 'Golden Gate Park': 22, 'The Castro': 19, 'Marina District': 27, 'Union Square': 18, 'Sunset District': 23, 'Alamo Square': 16, 'Financial District': 19, 'Mission District': 13},
    'Marina District': {'Pacific Heights': 7, 'Golden Gate Park': 18, 'The Castro': 22, 'Bayview': 27, 'Union Square': 16, 'Sunset District': 19, 'Alamo Square': 15, 'Financial District': 17, 'Mission District': 20},
    'Union Square': {'Pacific Heights': 15, 'Golden Gate Park': 22, 'The Castro': 17, 'Bayview': 15, 'Marina District': 18, 'Sunset District': 27, 'Alamo Square': 15, 'Financial District': 9, 'Mission District': 14},
    'Sunset District': {'Pacific Heights': 21, 'Golden Gate Park': 11, 'The Castro': 17, 'Bayview': 22, 'Marina District': 21, 'Union Square': 30, 'Alamo Square': 17, 'Financial District': 30, 'Mission District': 25},
    'Alamo Square': {'Pacific Heights': 10, 'Golden Gate Park': 9, 'The Castro': 8, 'Bayview': 16, 'Marina District': 15, 'Union Square': 14, 'Sunset District': 16, 'Financial District': 17, 'Mission District': 10},
    'Financial District': {'Pacific Heights': 13, 'Golden Gate Park': 23, 'The Castro': 20, 'Bayview': 19, 'Marina District': 15, 'Union Square': 9, 'Sunset District': 30, 'Alamo Square': 17, 'Mission District': 17},
    'Mission District': {'Pacific Heights': 16, 'Golden Gate Park': 17, 'The Castro': 7, 'Bayview': 14, 'Marina District': 19, 'Union Square': 15, 'Sunset District': 24, 'Alamo Square': 11, 'Financial District': 15}
}

friends = [
    {'name': 'Deborah', 'location': 'Bayview', 'available_start': '08:30', 'available_end': '12:00', 'min_duration': 30},
    {'name': 'Matthew', 'location': 'Marina District', 'available_start': '09:15', 'available_end': '14:15', 'min_duration': 45},
    {'name': 'Helen', 'location': 'Golden Gate Park', 'available_start': '09:30', 'available_end': '12:15', 'min_duration': 45},
    {'name': 'Joseph', 'location': 'Union Square', 'available_start': '14:15', 'available_end': '18:45', 'min_duration': 120},
    {'name': 'Rebecca', 'location': 'Financial District', 'available_start': '14:45', 'available_end': '16:15', 'min_duration': 30},
    {'name': 'Ronald', 'location': 'Sunset District', 'available_start': '16:00', 'available_end': '20:45', 'min_duration': 60},
    {'name': 'Robert', 'location': 'Alamo Square', 'available_start': '18:30', 'available_end': '21:15', 'min_duration': 120},
    {'name': 'Elizabeth', 'location': 'Mission District', 'available_start': '18:30', 'available_end': '21:00', 'min_duration': 120},
    {'name': 'Steven', 'location': 'The Castro', 'available_start': '20:15', 'available_end': '22:00', 'min_duration': 105}
]

def time_to_minutes(time_str):
    hh, mm = map(int, time_str.split(':'))
    return hh * 60 + mm

def minutes_to_time(minutes):
    hh = minutes // 60
    mm = minutes % 60
    return f"{hh:02d}:{mm:02d}"

solver = Optimize()

# Create variables and constraints
meetings = []
for friend in friends:
    start = Int(f"start_{friend['name']}")
    end = Int(f"end_{friend['name']}")
    duration = end - start
    
    solver.add(start >= time_to_minutes(friend['available_start']))
    solver.add(end <= time_to_minutes(friend['available_end']))
    solver.add(duration >= friend['min_duration'])
    solver.add(start < end)
    
    meetings.append({
        'name': friend['name'],
        'location': friend['location'],
        'start': start,
        'end': end
    })

# Create sequence variables to determine meeting order
order = [Int(f"order_{i}") for i in range(len(meetings))]
solver.add(Distinct(order))
for i in range(len(meetings)):
    solver.add(order[i] >= 0)
    solver.add(order[i] < len(meetings))

# Add travel time constraints based on ordering
for i in range(len(meetings)):
    for j in range(len(meetings)):
        if i != j:
            # If meeting i comes before meeting j in the order
            loc_i = meetings[i]['location']
            loc_j = meetings[j]['location']
            travel = travel_times[loc_i][loc_j]
            
            solver.add(Implies(
                order[i] < order[j],
                meetings[i]['end'] + travel <= meetings[j]['start']
            ))

# Starting constraint
solver.add(meetings[0]['start'] >= time_to_minutes("09:00"))

# Try to maximize total meeting time
total_time = sum([meetings[i]['end'] - meetings[i]['start'] for i in range(len(meetings))])
solver.maximize(total_time)

if solver.check() == sat:
    model = solver.model()
    itinerary = []
    # Sort meetings by their order in the solution
    ordered_meetings = sorted(
        [(model.evaluate(order[i]).as_long(), meetings[i]) for i in range(len(meetings))],
        key=lambda x: x[0]
    )
    for _, meeting in ordered_meetings:
        start = model[meeting['start']].as_long()
        end = model[meeting['end']].as_long()
        itinerary.append({
            "action": "meet",
            "person": meeting['name'],
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No valid schedule found.")