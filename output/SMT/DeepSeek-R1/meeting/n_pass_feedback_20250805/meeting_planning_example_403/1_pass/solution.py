from z3 import *
import json

def main():
    travel_dict = {
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'The Castro'): 19,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Presidio'): 11,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Pacific Heights', 'The Castro'): 16,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Pacific Heights'): 11,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'The Castro'): 21,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Pacific Heights'): 10,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'The Castro'): 22,
        ('The Castro', 'Union Square'): 19,
        ('The Castro', 'Golden Gate Park'): 11,
        ('The Castro', 'Pacific Heights'): 16,
        ('The Castro', 'Presidio'): 20,
        ('The Castro', 'Chinatown'): 20
    }

    friends = ['Andrew', 'Sarah', 'Nancy', 'Rebecca', 'Robert']
    locations = {
        'Andrew': 'Golden Gate Park',
        'Sarah': 'Pacific Heights',
        'Nancy': 'Presidio',
        'Rebecca': 'Chinatown',
        'Robert': 'The Castro'
    }
    avail_start_min = [165, 435, 510, 45, 0]
    avail_end_min = [330, 585, 615, 750, 315]
    min_dur_min = [75, 15, 60, 90, 30]

    n = len(friends)
    opt = Optimize()

    meet = [Bool(f'meet_{i}') for i in range(n)]
    s = [Int(f's_{i}') for i in range(n)]

    for i in range(n):
        loc_i = locations[friends[i]]
        from_union = travel_dict[('Union Square', loc_i)]
        opt.add(Implies(meet[i], s[i] >= from_union))
        opt.add(Implies(meet[i], s[i] >= avail_start_min[i]))
        opt.add(Implies(meet[i], s[i] + min_dur_min[i] <= avail_end_min[i]))

    for i in range(n):
        for j in range(i+1, n):
            loc_i = locations[friends[i]]
            loc_j = locations[friends[j]]
            time_ij = travel_dict[(loc_i, loc_j)]
            time_ji = travel_dict[(loc_j, loc_i)]
            constraint = Or(
                s[j] >= s[i] + min_dur_min[i] + time_ij,
                s[i] >= s[j] + min_dur_min[j] + time_ji
            )
            opt.add(Implies(And(meet[i], meet[j]), constraint))

    total_meet = Sum([If(meet[i], 1, 0) for i in range(n)])
    opt.maximize(total_meet)

    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for i in range(n):
            if m.evaluate(meet[i]):
                start_val = m.evaluate(s[i]).as_long()
                hour_abs = 9 + start_val // 60
                minute_abs = start_val % 60
                start_time = f"{hour_abs:02d}:{minute_abs:02d}"

                end_val = start_val + min_dur_min[i]
                hour_end = 9 + end_val // 60
                minute_end = end_val % 60
                end_time = f"{hour_end:02d}:{minute_end:02d}"

                itinerary.append({
                    "action": "meet",
                    "person": friends[i],
                    "start_time": start_time,
                    "end_time": end_time
                })
        itinerary.sort(key=lambda x: x['start_time'])
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()