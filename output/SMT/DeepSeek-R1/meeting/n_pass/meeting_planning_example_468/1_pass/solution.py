from z3 import *
import json

def main():
    travel_dict = {
        'The Castro': {
            'Bayview': 19,
            'Pacific Heights': 16,
            'Alamo Square': 8,
            'Fisherman\'s Wharf': 24,
            'Golden Gate Park': 11
        },
        'Bayview': {
            'The Castro': 20,
            'Pacific Heights': 23,
            'Alamo Square': 16,
            'Fisherman\'s Wharf': 25,
            'Golden Gate Park': 22
        },
        'Pacific Heights': {
            'The Castro': 16,
            'Bayview': 22,
            'Alamo Square': 10,
            'Fisherman\'s Wharf': 13,
            'Golden Gate Park': 15
        },
        'Alamo Square': {
            'The Castro': 8,
            'Bayview': 16,
            'Pacific Heights': 10,
            'Fisherman\'s Wharf': 19,
            'Golden Gate Park': 9
        },
        'Fisherman\'s Wharf': {
            'The Castro': 26,
            'Bayview': 26,
            'Pacific Heights': 12,
            'Alamo Square': 20,
            'Golden Gate Park': 25
        },
        'Golden Gate Park': {
            'The Castro': 13,
            'Bayview': 23,
            'Pacific Heights': 16,
            'Alamo Square': 10,
            'Fisherman\'s Wharf': 24
        }
    }

    friends = [
        ('Rebecca', 'Bayview', 540, 765),      # 9:00AM to 12:45PM
        ('Amanda', 'Pacific Heights', 1110, 1305), # 6:30PM to 9:45PM
        ('James', 'Alamo Square', 585, 1275),   # 9:45AM to 9:15PM
        ('Sarah', 'Fisherman\'s Wharf', 480, 1290), # 8:00AM to 9:30PM
        ('Melissa', 'Golden Gate Park', 540, 1125)  # 9:00AM to 6:45PM
    ]

    n_meetings = 6  # 1 dummy + 5 friends
    meet = [None] * n_meetings
    start = [None] * n_meetings
    end = [None] * n_meetings
    loc = [None] * n_meetings

    # Dummy meeting at The Castro
    loc[0] = 'The Castro'
    start[0] = 540  # 9:00AM in minutes from midnight
    end[0] = 540

    s = Optimize()

    # Initialize variables for friends (indices 1 to 5)
    for i in range(1, n_meetings):
        name, location, avail_start, avail_end = friends[i-1]
        meet[i] = Bool(f'meet_{name}')
        start[i] = Int(f'start_{name}')
        end[i] = start[i] + 90
        loc[i] = location

        # If meeting this friend, enforce availability constraints
        s.add(Implies(meet[i], start[i] >= avail_start))
        s.add(Implies(meet[i], end[i] <= avail_end))

    # Disjunctive constraints for every pair of meetings (including dummy)
    for i in range(n_meetings):
        for j in range(i+1, n_meetings):
            if i == 0:  # Dummy meeting
                s.add(Implies(meet[j], Or(
                    start[j] >= end[i] + travel_dict[loc[i]][loc[j]],
                    start[i] >= end[j] + travel_dict[loc[j]][loc[i]]
                )))
            else:
                s.add(Implies(And(meet[i], meet[j]), Or(
                    start[j] >= end[i] + travel_dict[loc[i]][loc[j]],
                    start[i] >= end[j] + travel_dict[loc[j]][loc[i]]
                )))

    # Maximize the number of friends met
    s.maximize(Sum([If(meet[i], 1, 0) for i in range(1, n_meetings)]))

    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(1, n_meetings):
            if is_true(m[meet[i]]):
                name = friends[i-1][0]
                start_val = m[start[i]].as_long()
                end_val = start_val + 90
                start_hour = start_val // 60
                start_min = start_val % 60
                end_hour = end_val // 60
                end_min = end_val % 60
                start_time = f"{start_hour:02d}:{start_min:02d}"
                end_time = f"{end_hour:02d}:{end_min:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_time,
                    "end_time": end_time
                })
        itinerary.sort(key=lambda x: x['start_time'])
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()