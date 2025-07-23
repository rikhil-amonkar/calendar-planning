from z3 import *

def solve_scheduling_problem():
    # Define the travel times between locations
    travel_times = {
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Presidio', 'Alamo Square'): 19,
        ('Presidio', 'Financial District'): 23,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Richmond District'): 7,
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Alamo Square'): 21,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Fisherman\'s Wharf', 'Union Square'): 13,
        ('Fisherman\'s Wharf', 'Sunset District'): 27,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Chinatown'): 12,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Alamo Square', 'Financial District'): 17,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'Embarcadero'): 16,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Chinatown'): 15,
        ('Alamo Square', 'Richmond District'): 11,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'Union Square'): 9,
        ('Financial District', 'Sunset District'): 30,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Richmond District'): 21,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Fisherman\'s Wharf'): 15,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Sunset District'): 27,
        ('Union Square', 'Embarcadero'): 11,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Richmond District'): 20,
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', 'Fisherman\'s Wharf'): 29,
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Financial District'): 30,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Embarcadero'): 30,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Richmond District'): 12,
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Embarcadero', 'Financial District'): 5,
        ('Embarcadero', 'Union Square'): 10,
        ('Embarcadero', 'Sunset District'): 30,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Richmond District'): 21,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Alamo Square'): 9,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Fisherman\'s Wharf'): 8,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'Embarcadero'): 5,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Richmond District'): 20,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Alamo Square'): 13,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'Union Square'): 21,
        ('Richmond District', 'Sunset District'): 11,
        ('Richmond District', 'Embarcadero'): 19,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Richmond District', 'Chinatown'): 20,
    }

    # Define friends and their availability
    friends = {
        'Jeffrey': {'location': 'Fisherman\'s Wharf', 'start': '10:15', 'end': '13:00', 'duration': 90},
        'Ronald': {'location': 'Alamo Square', 'start': '07:45', 'end': '14:45', 'duration': 120},
        'Jason': {'location': 'Financial District', 'start': '10:45', 'end': '16:00', 'duration': 105},
        'Melissa': {'location': 'Union Square', 'start': '17:45', 'end': '18:15', 'duration': 15},
        'Elizabeth': {'location': 'Sunset District', 'start': '14:45', 'end': '17:30', 'duration': 105},
        'Margaret': {'location': 'Embarcadero', 'start': '13:15', 'end': '19:00', 'duration': 90},
        'George': {'location': 'Golden Gate Park', 'start': '19:00', 'end': '22:00', 'duration': 75},
        'Richard': {'location': 'Chinatown', 'start': '09:30', 'end': '21:00', 'duration': 15},
        'Laura': {'location': 'Richmond District', 'start': '09:45', 'end': '18:00', 'duration': 60},
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    # Initialize Z3 optimizer
    opt = Optimize()

    # Variables for each meeting: start time, end time, and whether the meeting is scheduled
    meetings = {}
    for name in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        scheduled = Bool(f'scheduled_{name}')
        meetings[name] = {'start': start, 'end': end, 'scheduled': scheduled}

    # Current location starts at Presidio at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes

    # Constraints for each meeting
    for name, data in friends.items():
        loc = data['location']
        friend_start = time_to_minutes(data['start'])
        friend_end = time_to_minutes(data['end'])
        duration = data['duration']

        # If meeting is scheduled, it must be within friend's availability and meet duration
        opt.add(Implies(meetings[name]['scheduled'], 
                     And(meetings[name]['start'] >= friend_start,
                         meetings[name]['end'] <= friend_end,
                         meetings[name]['end'] == meetings[name]['start'] + duration)))

        # If meeting is not scheduled, start and end times are irrelevant
        opt.add(Implies(Not(meetings[name]['scheduled']), 
                     And(meetings[name]['start'] == -1,
                         meetings[name]['end'] == -1)))

    # Order of meetings and travel times
    # We need to ensure sequential meetings with proper travel times
    meeting_names = list(friends.keys())
    n = len(meeting_names)
    
    # Create variables for meeting order
    order = [Int(f'order_{i}') for i in range(n)]
    opt.add(Distinct(order))
    opt.add([And(order[i] >= 0, order[i] < n) for i in range(n)])

    # Create variables for arrival and departure times
    arrival = [Int(f'arrival_{i}') for i in range(n)]
    departure = [Int(f'departure_{i}') for i in range(n)]
    location = [String(f'location_{i}') for i in range(n)]

    # Initial conditions
    opt.add(arrival[0] == current_time)
    opt.add(location[0] == 'Presidio')

    # Constraints for sequential meetings
    for i in range(n):
        name = meeting_names[i]
        loc = friends[name]['location']
        opt.add(Implies(meetings[name]['scheduled'], 
                       arrival[i] == meetings[name]['start']))
        opt.add(Implies(meetings[name]['scheduled'], 
                       departure[i] == meetings[name]['end']))
        opt.add(Implies(meetings[name]['scheduled'], 
                       location[i] == loc))

        for j in range(n):
            if i != j:
                # Ensure no overlapping meetings
                opt.add(Implies(And(meetings[name]['scheduled'], meetings[meeting_names[j]]['scheduled']),
                              Or(meetings[name]['end'] <= meetings[meeting_names[j]]['start'],
                                 meetings[meeting_names[j]]['end'] <= meetings[name]['start'])))
                
                # Travel time constraints
                travel = travel_times.get((friends[meeting_names[i]]['location'], 
                                         friends[meeting_names[j]]['location']), 0)
                opt.add(Implies(And(order[i] < order[j], 
                                  meetings[name]['scheduled'], 
                                  meetings[meeting_names[j]]['scheduled']),
                              meetings[meeting_names[j]]['start'] >= meetings[name]['end'] + travel))

    # Maximize the number of friends met
    total_met = Sum([If(meetings[name]['scheduled'], 1, 0) for name in friends])
    opt.maximize(total_met)

    # Solve the problem
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for name in friends:
            if m.evaluate(meetings[name]['scheduled']):
                start = m.evaluate(meetings[name]['start']).as_long()
                end = m.evaluate(meetings[name]['end']).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x['start_time']))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the solver and print the result
result = solve_scheduling_problem()
print(result)