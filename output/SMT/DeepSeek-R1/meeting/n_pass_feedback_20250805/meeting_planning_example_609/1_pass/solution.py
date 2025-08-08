from z3 import *
import json

def main():
    friends = ['David', 'Kenneth', 'John', 'Charles', 'Deborah', 'Karen']
    locations = {
        'David': 'Mission District',
        'Kenneth': 'Alamo Square',
        'John': 'Pacific Heights',
        'Charles': 'Union Square',
        'Deborah': 'Golden Gate Park',
        'Karen': 'Sunset District'
    }
    available_start = {
        'David': 8 * 60,       # 8:00 AM
        'Kenneth': 14 * 60,     # 2:00 PM
        'John': 17 * 60,        # 5:00 PM
        'Charles': 21 * 60 + 45, # 9:45 PM
        'Deborah': 7 * 60,      # 7:00 AM
        'Karen': 17 * 60 + 45   # 5:45 PM
    }
    available_end = {
        'David': 19 * 60 + 45,  # 7:45 PM
        'Kenneth': 19 * 60 + 45, # 7:45 PM
        'John': 20 * 60,        # 8:00 PM
        'Charles': 22 * 60 + 45, # 10:45 PM
        'Deborah': 18 * 60 + 15, # 6:15 PM
        'Karen': 21 * 60 + 15   # 9:15 PM
    }
    min_duration = {
        'David': 45,
        'Kenneth': 120,
        'John': 15,
        'Charles': 60,
        'Deborah': 90,
        'Karen': 15
    }

    travel = {
        'Chinatown': {
            'Mission District': 18,
            'Alamo Square': 17,
            'Pacific Heights': 10,
            'Union Square': 7,
            'Golden Gate Park': 23,
            'Sunset District': 29,
            'Presidio': 19
        },
        'Mission District': {
            'Chinatown': 16,
            'Alamo Square': 11,
            'Pacific Heights': 16,
            'Union Square': 15,
            'Golden Gate Park': 17,
            'Sunset District': 24,
            'Presidio': 25
        },
        'Alamo Square': {
            'Chinatown': 16,
            'Mission District': 10,
            'Pacific Heights': 10,
            'Union Square': 14,
            'Golden Gate Park': 9,
            'Sunset District': 16,
            'Presidio': 18
        },
        'Pacific Heights': {
            'Chinatown': 11,
            'Mission District': 15,
            'Alamo Square': 10,
            'Union Square': 12,
            'Golden Gate Park': 15,
            'Sunset District': 21,
            'Presidio': 11
        },
        'Union Square': {
            'Chinatown': 7,
            'Mission District': 14,
            'Alamo Square': 15,
            'Pacific Heights': 15,
            'Golden Gate Park': 22,
            'Sunset District': 26,
            'Presidio': 24
        },
        'Golden Gate Park': {
            'Chinatown': 23,
            'Mission District': 17,
            'Alamo Square': 10,
            'Pacific Heights': 16,
            'Union Square': 22,
            'Sunset District': 10,
            'Presidio': 11
        },
        'Sunset District': {
            'Chinatown': 30,
            'Mission District': 24,
            'Alamo Square': 17,
            'Pacific Heights': 21,
            'Union Square': 30,
            'Golden Gate Park': 11,
            'Presidio': 16
        },
        'Presidio': {
            'Chinatown': 21,
            'Mission District': 26,
            'Alamo Square': 18,
            'Pacific Heights': 11,
            'Union Square': 22,
            'Golden Gate Park': 12,
            'Sunset District': 15
        }
    }

    s = Solver()
    opt = Optimize()
    
    meet_vars = {f: Bool(f'meet_{f}') for f in friends}
    start_vars = {f: Int(f'start_{f}') for f in friends}
    end_vars = {f: start_vars[f] + min_duration[f] for f in friends}
    
    for f in friends:
        loc = locations[f]
        opt.add(Implies(meet_vars[f], start_vars[f] >= available_start[f]))
        opt.add(Implies(meet_vars[f], end_vars[f] <= available_end[f]))
        opt.add(Implies(meet_vars[f], start_vars[f] >= 540 + travel['Chinatown'][loc]))
    
    for i in range(len(friends)):
        for j in range(i + 1, len(friends)):
            f1 = friends[i]
            f2 = friends[j]
            loc1 = locations[f1]
            loc2 = locations[f2]
            cond = And(meet_vars[f1], meet_vars[f2])
            c = Or(
                start_vars[f1] >= end_vars[f2] + travel[loc2][loc1],
                start_vars[f2] >= end_vars[f1] + travel[loc1][loc2]
            )
            opt.add(Implies(cond, c))
    
    goal = Sum([If(meet_vars[f], 1, 0) for f in friends])
    opt.maximize(goal)
    
    itinerary = []
    if opt.check() == sat:
        model = opt.model()
        for f in friends:
            if model.eval(meet_vars[f]):
                start_val = model.eval(start_vars[f])
                start_min = start_val.as_long()
                end_min = start_min + min_duration[f]
                start_time = f"{start_min // 60:02d}:{start_min % 60:02d}"
                end_time = f"{end_min // 60:02d}:{end_min % 60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": f,
                    "start_time": start_time,
                    "end_time": end_time
                })
        itinerary.sort(key=lambda x: x['start_time'])
    
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()