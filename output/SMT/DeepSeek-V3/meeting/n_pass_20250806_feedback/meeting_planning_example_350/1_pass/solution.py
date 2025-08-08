from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the travel times as a dictionary for easy lookup
    travel_times = {
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Financial District'): 19,
        ('Pacific Heights', 'Bayview'): 22,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Pacific Heights', 'Financial District'): 13,
        ('Mission District', 'Bayview'): 15,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Financial District'): 17,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Financial District'): 21,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'Mission District'): 17,
        ('Financial District', 'Haight-Ashbury'): 19,
    }

    # Define the friends' availability and constraints
    friends = [
        {
            'name': 'Mary',
            'location': 'Pacific Heights',
            'start_window': 10 * 60,  # 10:00 AM in minutes
            'end_window': 19 * 60,    # 7:00 PM in minutes
            'min_duration': 45,
        },
        {
            'name': 'Lisa',
            'location': 'Mission District',
            'start_window': 20 * 60 + 30,  # 8:30 PM in minutes
            'end_window': 22 * 60,        # 10:00 PM in minutes
            'min_duration': 75,
        },
        {
            'name': 'Betty',
            'location': 'Haight-Ashbury',
            'start_window': 7 * 60 + 15,  # 7:15 AM in minutes
            'end_window': 17 * 60 + 15,   # 5:15 PM in minutes
            'min_duration': 90,
        },
        {
            'name': 'Charles',
            'location': 'Financial District',
            'start_window': 11 * 60 + 15,  # 11:15 AM in minutes
            'end_window': 15 * 60,         # 3:00 PM in minutes
            'min_duration': 120,
        }
    ]

    # Current time starts at 9:00 AM (540 minutes)
    current_time = 540
    current_location = 'Bayview'

    # Variables to track meetings
    meetings = []
    itinerary = []

    # For each friend, create variables for meeting start and end times
    for friend in friends:
        start = Int(f'start_{friend["name"]}')
        end = Int(f'end_{friend["name"]}')
        s.add(start >= friend['start_window'])
        s.add(end <= friend['end_window'])
        s.add(end - start >= friend['min_duration'])
        meetings.append({
            'name': friend['name'],
            'location': friend['location'],
            'start': start,
            'end': end,
            'min_duration': friend['min_duration']
        })

    # Constraints to ensure meetings do not overlap and travel times are respected
    # We need to decide the order of meetings. Here, we'll try all permutations or use a heuristic.
    # For simplicity, we'll assume an order and adjust constraints accordingly.
    # This is a simplified approach; a more comprehensive solution would explore all possible orders.

    # Let's assume the order is Betty -> Mary -> Charles -> Lisa
    # This is a heuristic based on their time windows.

    # Betty (Haight-Ashbury)
    betty = next(f for f in meetings if f['name'] == 'Betty')
    # Travel from Bayview to Haight-Ashbury: 19 minutes
    s.add(betty['start'] >= current_time + travel_times[(current_location, betty['location'])])

    # Mary (Pacific Heights)
    mary = next(f for f in meetings if f['name'] == 'Mary')
    # Travel from Haight-Ashbury to Pacific Heights: 12 minutes
    s.add(mary['start'] >= betty['end'] + travel_times[(betty['location'], mary['location'])])

    # Charles (Financial District)
    charles = next(f for f in meetings if f['name'] == 'Charles')
    # Travel from Pacific Heights to Financial District: 13 minutes
    s.add(charles['start'] >= mary['end'] + travel_times[(mary['location'], charles['location'])])

    # Lisa (Mission District)
    lisa = next(f for f in meetings if f['name'] == 'Lisa')
    # Travel from Financial District to Mission District: 17 minutes
    s.add(lisa['start'] >= charles['end'] + travel_times[(charles['location'], lisa['location'])])

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        # Collect the meeting times
        itinerary = []
        for friend in friends:
            start_val = model.eval(Int(f'start_{friend["name"]}')).as_long()
            end_val = model.eval(Int(f'end_{friend["name"]}')).as_long()
            # Convert minutes to HH:MM format
            start_hh = start_val // 60
            start_mm = start_val % 60
            end_hh = end_val // 60
            end_mm = end_val % 60
            itinerary.append({
                "action": "meet",
                "person": friend["name"],
                "start_time": f"{start_hh:02d}:{start_mm:02d}",
                "end_time": f"{end_hh:02d}:{end_mm:02d}"
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling()
print(result)