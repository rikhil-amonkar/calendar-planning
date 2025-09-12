import z3
import json

# Define the people and their constraints
people = [
    {
        'name': 'Brian',
        'location': 'North Beach',
        'available_start': 13 * 60,  # 1:00 PM
        'available_end': 19 * 60,    # 7:00 PM
        'required_duration': 90,
    },
    {
        'name': 'Richard',
        'location': "Fisherman's Wharf",
        'available_start': 11 * 60,  # 11:00 AM
        'available_end': 12 * 60 + 45,  # 12:45 PM
        'required_duration': 60,
    },
    {
        'name': 'Ashley',
        'location': 'Haight-Ashbury',
        'available_start': 15 * 60,  # 3:00 PM
        'available_end': 20 * 60 + 30,  # 8:30 PM
        'required_duration': 90,
    },
    {
        'name': 'Elizabeth',
        'location': 'Nob Hill',
        'available_start': 11 * 60 + 45,  # 11:45 AM
        'available_end': 18 * 60 + 30,  # 6:30 PM
        'required_duration': 75,
    },
    {
        'name': 'Jessica',
        'location': 'Golden Gate Park',
        'available_start': 20 * 60,  # 8:00 PM
        'available_end': 21 * 60 + 45,  # 9:45 PM
        'required_duration': 105,
    },
    {
        'name': 'Deborah',
        'location': 'Union Square',
        'available_start': 17 * 60 + 30,  # 5:30 PM
        'available_end': 22 * 60,  # 10:00 PM
        'required_duration': 60,
    },
    {
        'name': 'Kimberly',
        'location': 'Alamo Square',
        'available_start': 17 * 60 + 30,  # 5:30 PM
        'available_end': 21 * 60 + 15,  # 9:15 PM
        'required_duration': 45,
    },
    {
        'name': 'Matthew',
        'location': 'Presidio',
        'available_start': 8 * 60 + 15,  # 8:15 AM
        'available_end': 9 * 60,  # 9:00 AM
        'required_duration': 15,
    },
    {
        'name': 'Kenneth',
        'location': 'Chinatown',
        'available_start': 13 * 60 + 45,  # 1:45 PM
        'available_end': 19 * 60 + 30,  # 7:30 PM
        'required_duration': 105,
    },
    {
        'name': 'Anthony',
        'location': 'Pacific Heights',
        'available_start': 14 * 60 + 15,  # 2:15 PM
        'available_end': 16 * 60,  # 4:00 PM
        'required_duration': 30,
    },
]

# Define the travel times between locations
travel_times = {
    ('Bayview', 'North Beach'): 22,
    ('Bayview', "Fisherman's Wharf"): 25,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Presidio'): 32,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Pacific Heights'): 23,
    ("Fisherman's Wharf", 'Bayview'): 26,
    ("Fisherman's Wharf", 'North Beach'): 6,
    ("Fisherman's Wharf", 'Haight-Ashbury'): 22,
    ("Fisherman's Wharf", 'Nob Hill'): 11,
    ("Fisherman's Wharf", 'Golden Gate Park'): 25,
    ("Fisherman's Wharf", 'Union Square'): 13,
    ("Fisherman's Wharf", 'Alamo Square'): 21,
    ("Fisherman's Wharf", 'Presidio'): 17,
    ("Fisherman's Wharf", 'Chinatown'): 12,
    ("Fisherman's Wharf", 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', "Fisherman's Wharf"): 23,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', "Fisherman's Wharf"): 10,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', "Fisherman's Wharf"): 24,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', "Fisherman's Wharf"): 15,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Pacific Heights'): 15,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', "Fisherman's Wharf"): 19,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', "Fisherman's Wharf"): 19,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Pacific Heights'): 11,
    ('Chinatown', 'Bayview'): 20,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', "Fisherman's Wharf"): 8,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', "Fisherman's Wharf"): 13,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Presidio'): 11,
    ('Pacific Heights', 'Chinatown'): 11,
}

# Create Z3 solver
opt = z3.Optimize()

meet_vars = []
s_vars = []
e_vars = []

for person in people:
    name = person['name']
    location = person['location']
    available_start = person['available_start']
    available_end = person['available_end']
    duration = person['required_duration']
    travel_time_bayview = travel_times[('Bayview', location)]

    # Create variables
    meet = z3.Bool(f'meet_{name}')
    s = z3.Int(f's_{name}')
    e = z3.Int(f'e_{name}')

    meet_vars.append(meet)
    s_vars.append(s)
    e_vars.append(e)

    # Add constraints if meet is true
    opt.add(z3.Implies(meet, s >= available_start))
    opt.add(z3.Implies(meet, e == s + duration))
    opt.add(z3.Implies(meet, e <= available_end))
    opt.add(z3.Implies(meet, s >= 540 + travel_time_bayview))  # 9:00 AM is 540 minutes

    # Store for later use
    person['meet'] = meet
    person['s'] = s
    person['e'] = e

# Add pairwise constraints
for i in range(len(people)):
    for j in range(len(people)):
        if i == j:
            continue
        p1 = people[i]
        p2 = people[j]
        loc1 = p1['location']
        loc2 = p2['location']
        duration1 = p1['required_duration']
        duration2 = p2['required_duration']
        travel_time1_to_2 = travel_times[(loc1, loc2)]
        travel_time2_to_1 = travel_times[(loc2, loc1)]
        meet1 = p1['meet']
        meet2 = p2['meet']
        s1 = p1['s']
        s2 = p2['s']

        # Add constraint: if both meet, then either p1 before p2 or p2 before p1
        constraint = z3.Implies(
            z3.And(meet1, meet2),
            z3.Or(
                s1 + duration1 + travel_time1_to_2 <= s2,
                s2 + duration2 + travel_time2_to_1 <= s1
            )
        )
        opt.add(constraint)

# Maximize the number of people met
num_meet = sum([z3.If(meet, 1, 0) for meet in meet_vars])
opt.maximize(num_meet)

# Check for solution
result = opt.check()
if result == z3.sat:
    model = opt.model()
    met_people = []
    for person in people:
        meet = model.eval(person['meet'])
        if meet:
            s = model.eval(person['s']).as_long()
            e = model.eval(person['e']).as_long()
            met_people.append({
                'person': person['name'],
                'location': person['location'],
                'start_time': s,
                'end_time': e
            })
    # Sort by start time
    met_people.sort(key=lambda x: x['start_time'])
    # Generate JSON
    itinerary = []
    for entry in met_people:
        start_time = entry['start_time']
        end_time = entry['end_time']
        start_h = start_time // 60
        start_m = start_time % 60
        end_h = end_time // 60
        end_m = end_time % 60
        itinerary.append({
            'action': 'meet',
            'location': entry['location'],
            'person': entry['person'],
            'start_time': f'{start_h}:{start_m:02d}',
            'end_time': f'{end_h}:{end_m:02d}'
        })
    print(json.dumps({'itinerary': itinerary}))
else:
    print(json.dumps({'itinerary': []}))