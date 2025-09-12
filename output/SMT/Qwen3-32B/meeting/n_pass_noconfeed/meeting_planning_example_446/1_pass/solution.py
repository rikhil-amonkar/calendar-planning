import z3
import json

def main():
    friends = [
        {
            'name': 'Kimberly',
            'location': 'Marina District',
            'available_start': 795,  # 1:15 PM
            'available_end': 1005,    # 4:45 PM
            'required_duration': 15
        },
        {
            'name': 'Robert',
            'location': 'Chinatown',
            'available_start': 735,  # 12:15 PM
            'available_end': 1215,    # 8:15 PM
            'required_duration': 15
        },
        {
            'name': 'Rebecca',
            'location': 'Financial District',
            'available_start': 795,  # 1:15 PM
            'available_end': 1005,    # 4:45 PM
            'required_duration': 75
        },
        {
            'name': 'Margaret',
            'location': 'Bayview',
            'available_start': 570,  # 9:30 AM
            'available_end': 810,    # 1:30 PM
            'required_duration': 30
        },
        {
            'name': 'Kenneth',
            'location': 'Union Square',
            'available_start': 1170, # 7:30 PM
            'available_end': 1275,   # 9:15 PM
            'required_duration': 75
        }
    ]

    travel_times = {
        ('Richmond District', 'Marina District'): 9,
        ('Richmond District', 'Chinatown'): 20,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'Bayview'): 26,
        ('Richmond District', 'Union Square'): 21,
        ('Marina District', 'Richmond District'): 11,
        ('Marina District', 'Chinatown'): 16,
        ('Marina District', 'Financial District'): 17,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Union Square'): 16,
        ('Chinatown', 'Richmond District'): 20,
        ('Chinatown', 'Marina District'): 12,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Bayview'): 22,
        ('Chinatown', 'Union Square'): 7,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'Marina District'): 15,
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Union Square'): 9,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Marina District'): 25,
        ('Bayview', 'Chinatown'): 18,
        ('Bayview', 'Financial District'): 19,
        ('Bayview', 'Union Square'): 17,
        ('Union Square', 'Richmond District'): 20,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Bayview'): 15,
    }

    solver = z3.Optimize()

    meet_vars = {}
    start_times = {}
    end_times = {}

    for friend in friends:
        name = friend['name']
        meet = z3.Bool(f'meet_{name}')
        start = z3.Int(f'start_{name}')
        end = z3.Int(f'end_{name}')
        meet_vars[name] = meet
        start_times[name] = start
        end_times[name] = end

        solver.add(z3.Implies(meet, start >= friend['available_start']))
        solver.add(z3.Implies(meet, end <= friend['available_end']))
        solver.add(z3.Implies(meet, end == start + friend['required_duration']))

        from_richmond = travel_times.get(('Richmond District', friend['location']), 0)
        solver.add(z3.Implies(meet, start >= 540 + from_richmond))

    for i in range(len(friends)):
        for j in range(i + 1, len(friends)):
            friendA = friends[i]
            friendB = friends[j]
            nameA = friendA['name']
            nameB = friendB['name']
            meetA = meet_vars[nameA]
            meetB = meet_vars[nameB]
            locA = friendA['location']
            locB = friendB['location']
            travel_A_to_B = travel_times.get((locA, locB), 0)
            travel_B_to_A = travel_times.get((locB, locA), 0)
            startA = start_times[nameA]
            endA = end_times[nameA]
            startB = start_times[nameB]
            endB = end_times[nameB]

            constraint = z3.Implies(
                z3.And(meetA, meetB),
                z3.Or(
                    endA + travel_A_to_B <= startB,
                    endB + travel_B_to_A <= startA
                )
            )
            solver.add(constraint)

    objective = z3.Sum([z3.If(meet, 1, 0) for meet in meet_vars.values()])
    solver.maximize(objective)

    if solver.check() == z3.sat:
        model = solver.model()
        itinerary = []
        for friend in friends:
            name = friend['name']
            meet = model.eval(meet_vars[name])
            if meet:
                start = model.eval(start_times[name]).as_long()
                end = model.eval(end_times[name]).as_long()
                def to_time_str(minutes):
                    hours = minutes // 60
                    mins = minutes % 60
                    return f"{hours}:{mins:02d}"
                itinerary.append({
                    "action": "meet",
                    "location": friend['location'],
                    "person": name,
                    "start_time": to_time_str(start),
                    "end_time": to_time_str(end)
                })
        itinerary.sort(key=lambda x: int(x['start_time'].replace(':', '')))
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()