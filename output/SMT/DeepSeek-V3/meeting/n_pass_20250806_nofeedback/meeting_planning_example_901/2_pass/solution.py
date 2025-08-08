from z3 import *
import json

def solve_scheduling_problem():
    s = Optimize()

    # Define all friends and their locations
    friends = {
        'Emily': 'Pacific Heights',
        'Helen': 'North Beach',
        'Kimberly': 'Golden Gate Park',
        'James': 'Embarcadero',
        'Linda': 'Haight-Ashbury',
        'Paul': 'Fisherman\'s Wharf',
        'Anthony': 'Mission District',
        'Nancy': 'Alamo Square',
        'William': 'Bayview',
        'Margaret': 'Richmond District'
    }

    # Travel times between locations (in minutes)
    travel_times = {
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Fisherman\'s Wharf'): 7,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Richmond District'): 14,
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Embarcadero'): 10,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Alamo Square'): 10,
        ('Pacific Heights', 'Bayview'): 22,
        ('Pacific Heights', 'Richmond District'): 12,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'Haight-Ashbury'): 18,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'Mission District'): 18,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Bayview'): 25,
        ('North Beach', 'Richmond District'): 18,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Alamo Square'): 9,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Embarcadero', 'Haight-Ashbury'): 21,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Mission District'): 20,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Richmond District'): 21,
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Alamo Square'): 5,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Fisherman\'s Wharf', 'Alamo Square'): 21,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Mission District', 'Alamo Square'): 10,
        ('Mission District', 'Bayview'): 14,
        ('Mission District', 'Richmond District'): 20,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Richmond District'): 11,
        ('Bayview', 'Richmond District'): 27
    }

    # Convert time windows to minutes since 9:00 AM (540)
    time_windows = {
        'Emily': (555, 825, 120),   # 9:15 AM - 1:45 PM, min 120 mins
        'Helen': (825, 1080, 30),    # 1:45 PM - 6:45 PM, min 30 mins
        'Kimberly': (1080, 1170, 75), # 6:45 PM - 9:15 PM, min 75 mins
        'James': (630, 690, 30),     # 10:30 AM - 11:30 AM, min 30 mins
        'Linda': (450, 1095, 15),    # 7:30 AM - 7:15 PM, min 15 mins
        'Paul': (855, 1080, 90),     # 2:45 PM - 6:45 PM, min 90 mins
        'Anthony': (480, 855, 105),   # 8:00 AM - 2:45 PM, min 105 mins
        'Nancy': (510, 825, 120),     # 8:30 AM - 1:45 PM, min 120 mins
        'William': (1050, 1170, 120), # 5:30 PM - 8:30 PM, min 120 mins
        'Margaret': (945, 1080, 45)   # 3:15 PM - 6:15 PM, min 45 mins
    }

    # Create variables for each meeting
    meeting_vars = {}
    for friend in friends:
        start = Int(f'{friend}_start')
        end = Int(f'{friend}_end')
        meeting_vars[friend] = (start, end)
        s.add(start >= time_windows[friend][0])
        s.add(end <= time_windows[friend][1])
        s.add(end - start >= time_windows[friend][2])

    # Create a list of all friends to visit
    all_friends = list(friends.keys())

    # Create variables to represent the order of visits
    position = {f: Int(f'pos_{f}') for f in all_friends}
    for f in all_friends:
        s.add(position[f] >= 0)
        s.add(position[f] < len(all_friends))

    # All positions must be distinct
    s.add(Distinct([position[f] for f in all_friends]))

    # Create variables for arrival and departure times at each location
    arrival = {f: Int(f'arrival_{f}') for f in all_friends}
    departure = {f: Int(f'departure_{f}') for f in all_friends}

    # Starting point: Russian Hill at 9:00 AM (540 minutes)
    first_visit = Int('first_visit')
    s.add(first_visit >= 0)
    s.add(first_visit < len(all_friends))
    first_friend = [If(first_visit == i, f, None) for i, f in enumerate(all_friends)]
    first_friend = [f for f in first_friend if f is not None][0]

    # Constraints for the first visit
    s.add(arrival[first_friend] == 540 + travel_times[('Russian Hill', friends[first_friend])])
    s.add(departure[first_friend] == arrival[first_friend] + (meeting_vars[first_friend][1] - meeting_vars[first_friend][0]))

    # Constraints for subsequent visits
    for f in all_friends:
        if f != first_friend:
            # Find the previous friend in the sequence
            prev_friends = [pf for pf in all_friends if pf != f]
            prev_arrival = [If(position[pf] < position[f], departure[pf], 0) for pf in prev_friends]
            prev_location = [If(position[pf] < position[f], friends[pf], 'Russian Hill') for pf in prev_friends]
            
            # Calculate travel time from previous location
            travel = [If(And(position[pf] < position[f], 
                         (prev_location[i], friends[f]) in travel_times),
                      travel_times[(prev_location[i], friends[f])],
                      If(And(position[pf] < position[f], 
                          (friends[f], prev_location[i]) in travel_times),
                       travel_times[(friends[f], prev_location[i])],
                       0))
                     for i, pf in enumerate(prev_friends)]
            
            # Arrival time is max of possible previous departures plus travel time
            s.add(arrival[f] == Max([p + t for p, t in zip(prev_arrival, travel)]))
            s.add(departure[f] == arrival[f] + (meeting_vars[f][1] - meeting_vars[f][0]))

    # Ensure all meetings happen within their time windows
    for f in all_friends:
        s.add(meeting_vars[f][0] >= arrival[f])
        s.add(meeting_vars[f][1] <= departure[f])

    # Maximize the number of friends met (all in this case)
    s.maximize(Sum([If(meeting_vars[f][1] > meeting_vars[f][0], 1, 0) for f in all_friends))

    if s.check() == sat:
        m = s.model()
        itinerary = []
        for f in all_friends:
            start = m.evaluate(meeting_vars[f][0]).as_long()
            end = m.evaluate(meeting_vars[f][1]).as_long()
            start_hh = start // 60
            start_mm = start % 60
            end_hh = end // 60
            end_mm = end % 60
            itinerary.append({
                "action": "meet",
                "person": f,
                "start_time": f"{start_hh:02d}:{start_mm:02d}",
                "end_time": f"{end_hh:02d}:{end_mm:02d}"
            })
        # Sort by start time
        itinerary.sort(key=lambda x: (int(x['start_time'][:2]), int(x['start_time'][3:])))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))