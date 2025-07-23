from z3 import *
import json

def solve_scheduling_problem():
    # Initialize solver
    s = Optimize()

    # Define travel times between locations (in minutes)
    travel_times = {
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Mission District'): 20,
        ('Richmond District', 'Bayview'): 26,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Fisherman\'s Wharf'): 22,
        ('Mission District', 'Richmond District'): 20,
        ('Mission District', 'Bayview'): 15,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Mission District'): 13,
    }

    # Define friends and their constraints
    friends = [
        {
            'name': 'Sarah',
            'location': 'Fisherman\'s Wharf',
            'available_start': (14, 45),  # 2:45 PM
            'available_end': (17, 30),    # 5:30 PM
            'min_duration': 105,
        },
        {
            'name': 'Mary',
            'location': 'Richmond District',
            'available_start': (13, 0),   # 1:00 PM
            'available_end': (19, 15),    # 7:15 PM
            'min_duration': 75,
        },
        {
            'name': 'Helen',
            'location': 'Mission District',
            'available_start': (21, 45),  # 9:45 PM
            'available_end': (22, 30),    # 10:30 PM
            'min_duration': 30,
        },
        {
            'name': 'Thomas',
            'location': 'Bayview',
            'available_start': (15, 15),  # 3:15 PM
            'available_end': (18, 45),    # 6:45 PM
            'min_duration': 120,
        }
    ]

    # Convert times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(hour, minute):
        return hour * 60 + minute - 540

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total_minutes = 540 + minutes
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"

    # Create variables for each meeting
    meeting_vars = {}
    for friend in friends:
        name = friend['name']
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meeting_vars[name] = (start, end, friend['location'])

        # Meeting must be within friend's availability
        s.add(start >= time_to_minutes(*friend['available_start']))
        s.add(end <= time_to_minutes(*friend['available_end']))
        s.add(end - start >= friend['min_duration'])

    # Create variables for meeting order
    order = [Int(f'order_{f["name"]}') for f in friends]
    s.add(Distinct(order))
    for i in range(len(friends)):
        s.add(order[i] >= 0, order[i] < len(friends))

    # Starting point
    current_location = 'Haight-Ashbury'
    start_time = 0

    # Create variables for arrival times
    arrival_times = {}
    for friend in friends:
        name = friend['name']
        arrival_times[name] = Int(f'arrival_{name}')

    # Constraints for travel between meetings
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                name_i = friends[i]['name']
                name_j = friends[j]['name']
                loc_i = friends[i]['location']
                loc_j = friends[j]['location']
                
                # If meeting i comes before meeting j
                s.add(Implies(
                    order[i] < order[j],
                    And(
                        arrival_times[name_j] >= meeting_vars[name_i][1] + travel_times.get((loc_i, loc_j), 0),
                        meeting_vars[name_j][0] >= arrival_times[name_j]
                    )
                ))

    # First meeting must be reachable from starting point
    for friend in friends:
        name = friend['name']
        s.add(Implies(
            order[friends.index(friend)] == 0,
            arrival_times[name] >= travel_times.get((current_location, friend['location']), 0)
        ))

    # Try to maximize the number of meetings
    num_meetings = Int('num_meetings')
    s.add(num_meetings == len(friends))  # Try to meet all friends
    s.maximize(num_meetings)

    # Check for solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend in friends:
            name = friend['name']
            start = model.eval(meeting_vars[name][0]).as_long()
            end = model.eval(meeting_vars[name][1]).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        # Sort by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))