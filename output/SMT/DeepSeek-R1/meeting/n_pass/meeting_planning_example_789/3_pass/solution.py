from z3 import *

def main():
    travel_dict = {
        ('Union Square', 'Russian Hill'): 13,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Sunset District'): 27,
        ('Russian Hill', 'Union Square'): 10,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Marina District'): 7,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Sunset District'): 23,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Alamo Square', 'Marina District'): 15,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Chinatown'): 15,
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', 'Sunset District'): 16,
        ('Haight-Ashbury', 'Union Square'): 19,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'Alamo Square'): 5,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'Russian Hill'): 8,
        ('Marina District', 'Alamo Square'): 15,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Presidio'): 10,
        ('Marina District', 'Sunset District'): 19,
        ('Bayview', 'Union Square'): 18,
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Marina District'): 27,
        ('Bayview', 'Chinatown'): 19,
        ('Bayview', 'Presidio'): 32,
        ('Bayview', 'Sunset District'): 23,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'Marina District'): 12,
        ('Chinatown', 'Bayview'): 20,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Sunset District'): 29,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'Russian Hill'): 14,
        ('Presidio', 'Alamo Square'): 19,
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Marina District'): 11,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Sunset District'): 15,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'Bayview'): 22,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Presidio'): 16
    }

    friends = [
        {'name': 'Betty', 'location': 'Russian Hill', 'start_avail': -120, 'end_avail': 465, 'min_duration': 105},
        {'name': 'Melissa', 'location': 'Alamo Square', 'start_avail': 30, 'end_avail': 495, 'min_duration': 105},
        {'name': 'Joshua', 'location': 'Haight-Ashbury', 'start_avail': 195, 'end_avail': 600, 'min_duration': 90},
        {'name': 'Jeffrey', 'location': 'Marina District', 'start_avail': 195, 'end_avail': 540, 'min_duration': 45},
        {'name': 'James', 'location': 'Bayview', 'start_avail': -90, 'end_avail': 660, 'min_duration': 90},
        {'name': 'Anthony', 'location': 'Chinatown', 'start_avail': 165, 'end_avail': 270, 'min_duration': 75},
        {'name': 'Timothy', 'location': 'Presidio', 'start_avail': 210, 'end_avail': 345, 'min_duration': 90},
        {'name': 'Emily', 'location': 'Sunset District', 'start_avail': 630, 'end_avail': 750, 'min_duration': 120}
    ]
    
    locations = [f['location'] for f in friends] + ['Union Square']
    n_friends = 8
    n_meetings = 9
    
    opt = Optimize()
    
    meet = [Bool(f"meet_{i}") for i in range(n_friends)]
    s = [Int(f"s_{i}") for i in range(n_meetings)]
    e = [Int(f"e_{i}") for i in range(n_meetings)]
    
    opt.add(s[8] == 0, e[8] == 0)
    
    before = {}
    for i in range(n_meetings):
        for j in range(i+1, n_meetings):
            before[(i, j)] = Bool(f"before_{i}_{j}")
    
    for i in range(n_friends):
        opt.add(Implies(meet[i], e[i] == s[i] + friends[i]['min_duration']))
        opt.add(Implies(meet[i], s[i] >= If(friends[i]['start_avail'] < 0, 0, friends[i]['start_avail'])))
        opt.add(Implies(meet[i], e[i] <= friends[i]['end_avail']))
        opt.add(Implies(meet[i], s[i] >= 0))
    
    for i in range(n_meetings):
        for j in range(i+1, n_meetings):
            held_i = meet[i] if i < n_friends else True
            held_j = meet[j] if j < n_friends else True
            
            loc_i = locations[i]
            loc_j = locations[j]
            travel_ij = travel_dict.get((loc_i, loc_j))
            travel_ji = travel_dict.get((loc_j, loc_i))
            if travel_ij is None or travel_ji is None:
                continue
                
            opt.add(Implies(And(held_i, held_j, before[(i,j)]), e[i] + travel_ij <= s[j]))
            opt.add(Implies(And(held_i, held_j, Not(before[(i,j)])), e[j] + travel_ji <= s[i]))
    
    opt.maximize(Sum([If(meet_i, 1, 0) for meet_i in meet]))
    
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for i in range(n_friends):
            if m.evaluate(meet[i]):
                start_val = m.evaluate(s[i]).as_long()
                end_val = m.evaluate(e[i]).as_long()
                start_hour = 9 + start_val // 60
                start_minute = start_val % 60
                end_hour = 9 + end_val // 60
                end_minute = end_val % 60
                start_time = f"{start_hour:02d}:{start_minute:02d}"
                end_time = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friends[i]['name'],
                    "start_time": start_time,
                    "end_time": end_time
                })
        itinerary.sort(key=lambda x: x['start_time'])
        print('SOLUTION:')
        print({'itinerary': itinerary})
    else:
        print("No solution found")

if __name__ == "__main__":
    main()