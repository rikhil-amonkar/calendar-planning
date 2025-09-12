import z3

def main():
    # Define locations and travel times
    locations = [
        'Russian Hill',
        'Sunset District',
        'Union Square',
        'Nob Hill',
        'Marina District',
        'Richmond District',
        'Financial District',
        'Embarcadero',
        'The Castro',
        'Alamo Square',
        'Presidio'
    ]
    travel_time = [
        [0, 23, 10, 5, 7, 14, 11, 8, 21, 15, 14],  # Russian Hill
        [24, 0, 30, 27, 21, 12, 30, 30, 17, 17, 16],  # Sunset District
        [13, 27, 0, 9, 18, 20, 9, 11, 17, 15, 24],  # Union Square
        [5, 24, 7, 0, 11, 14, 9, 9, 17, 11, 17],  # Nob Hill
        [8, 19, 16, 12, 0, 11, 17, 14, 22, 15, 10],  # Marina District
        [13, 11, 21, 17, 9, 0, 22, 19, 16, 13, 7],  # Richmond District
        [11, 30, 9, 8, 15, 21, 0, 4, 20, 17, 22],  # Financial District
        [8, 30, 10, 10, 12, 19, 5, 0, 25, 19, 20],  # Embarcadero
        [18, 17, 19, 16, 21, 16, 21, 22, 0, 8, 20],  # The Castro
        [13, 16, 14, 11, 15, 11, 17, 16, 8, 0, 17],  # Alamo Square
        [14, 15, 22, 18, 11, 7, 23, 20, 21, 19, 0]   # Presidio
    ]

    # Define friends
    friends = [
        {
            'name': 'David',
            'location_idx': 1,  # Sunset District
            'available_start': 9 * 60 + 15,  # 555
            'available_end': 22 * 60,  # 1320
            'min_duration': 15
        },
        {
            'name': 'Kenneth',
            'location_idx': 2,  # Union Square
            'available_start': 21 * 60 + 15,  # 1275
            'available_end': 21 * 60 + 45,  # 1305
            'min_duration': 15
        },
        {
            'name': 'Patricia',
            'location_idx': 3,  # Nob Hill
            'available_start': 15 * 60,  # 900 (3:00 PM)
            'available_end': 19 * 60 + 15,  # 1155 (7:15 PM)
            'min_duration': 120
        },
        {
            'name': 'Mary',
            'location_idx': 4,  # Marina District
            'available_start': 14 * 60 + 45,  # 885
            'available_end': 16 * 60 + 45,  # 1005
            'min_duration': 45
        },
        {
            'name': 'Charles',
            'location_idx': 5,  # Richmond District
            'available_start': 17 * 60 + 15,  # 1035
            'available_end': 21 * 60,  # 1260
            'min_duration': 15
        },
        {
            'name': 'Joshua',
            'location_idx': 6,  # Financial District
            'available_start': 14 * 60 + 30,  # 870
            'available_end': 17 * 60 + 15,  # 1035
            'min_duration': 90
        },
        {
            'name': 'Ronald',
            'location_idx': 7,  # Embarcadero
            'available_start': 18 * 60 + 15,  # 1095
            'available_end': 20 * 60 + 45,  # 1245
            'min_duration': 30
        },
        {
            'name': 'George',
            'location_idx': 8,  # The Castro
            'available_start': 14 * 60 + 15,  # 855
            'available_end': 19 * 60,  # 1140
            'min_duration': 105
        },
        {
            'name': 'Kimberly',
            'location_idx': 9,  # Alamo Square
            'available_start': 9 * 60,  # 540
            'available_end': 14 * 60 + 30,  # 870
            'min_duration': 105
        },
        {
            'name': 'William',
            'location_idx': 10,  # Presidio
            'available_start': 7 * 60,  # 420
            'available_end': 12 * 60 + 45,  # 765
            'min_duration': 60
        }
    ]

    N = len(friends)
    s = z3.Optimize()

    meet = [z3.Bool(f'meet_{i}') for i in range(N)]
    start = [z3.Int(f'start_{i}') for i in range(N)]
    end = [z3.Int(f'end_{i}') for i in range(N)]
    order = [z3.Int(f'order_{i}') for i in range(N)]

    # Constraints for each friend's meeting
    for i in range(N):
        s.add(z3.Implies(meet[i], z3.And(
            start[i] >= friends[i]['available_start'],
            end[i] == start[i] + friends[i]['min_duration'],
            end[i] <= friends[i]['available_end']
        )))

    # Uniqueness of order for met friends
    for i in range(N):
        for j in range(i + 1, N):
            s.add(z3.Implies(z3.And(meet[i], meet[j]), order[i] != order[j]))

    # Pairwise travel time constraints based on order
    for i in range(N):
        for j in range(N):
            if i != j:
                s.add(z3.Implies(
                    z3.And(meet[i], meet[j], order[i] < order[j]),
                    end[i] + travel_time[friends[i]['location_idx']][friends[j]['location_idx']] <= start[j]
                ))

    # Initial condition for the first meeting
    for i in range(N):
        s.add(z3.Implies(
            z3.And(meet[i], order[i] == 0),
            start[i] >= 9 * 60 + travel_time[0][friends[i]['location_idx']]
        ))

    # Ensure order variables are within bounds
    for i in range(N):
        s.add(order[i] >= 0)
        s.add(order[i] < N)

    # Maximize the number of met friends
    obj = z3.Sum([z3.If(meet[i], 1, 0) for i in range(N)])
    s.maximize(obj)

    if s.check() == z3.sat:
        model = s.model()
        itinerary = []
        for i in range(N):
            if model.eval(meet[i]):
                start_time = model.eval(start[i]).as_long()
                end_time = model.eval(end[i]).as_long()
                loc_idx = friends[i]['location_idx']
                location_name = locations[loc_idx]
                def to_time_str(t):
                    h = t // 60
                    m = t % 60
                    return f"{h}:{m:02d}"
                itinerary.append({
                    "action": "meet",
                    "location": location_name,
                    "person": friends[i]['name'],
                    "start_time": to_time_str(start_time),
                    "end_time": to_time_str(end_time)
                })
        itinerary.sort(key=lambda x: x['start_time'])
        import json
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()