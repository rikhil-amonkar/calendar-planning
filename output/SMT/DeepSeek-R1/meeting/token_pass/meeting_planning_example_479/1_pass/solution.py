from z3 import *
import json

def main():
    # Define travel times as a nested dictionary
    travel_times = {
        'Embarcadero': {
            'Golden Gate Park': 25,
            'Haight-Ashbury': 21,
            'Bayview': 21,
            'Presidio': 20,
            'Financial District': 5
        },
        'Golden Gate Park': {
            'Embarcadero': 25,
            'Haight-Ashbury': 7,
            'Bayview': 23,
            'Presidio': 11,
            'Financial District': 26
        },
        'Haight-Ashbury': {
            'Embarcadero': 20,
            'Golden Gate Park': 7,
            'Bayview': 18,
            'Presidio': 15,
            'Financial District': 21
        },
        'Bayview': {
            'Embarcadero': 19,
            'Golden Gate Park': 22,
            'Haight-Ashbury': 19,
            'Presidio': 31,
            'Financial District': 19
        },
        'Presidio': {
            'Embarcadero': 20,
            'Golden Gate Park': 12,
            'Haight-Ashbury': 15,
            'Bayview': 31,
            'Financial District': 23
        },
        'Financial District': {
            'Embarcadero': 4,
            'Golden Gate Park': 23,
            'Haight-Ashbury': 19,
            'Bayview': 19,
            'Presidio': 22
        }
    }

    # Convert time strings to minutes since 9:00 (540 minutes from midnight)
    def time_to_minutes(t):
        parts = t.replace('AM', '').replace('PM', '').split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        if 'PM' in t and hour != 12:
            hour += 12
        if 'AM' in t and hour == 12:
            hour = 0
        total_minutes = hour * 60 + minute
        return total_minutes - 540  # Offset from 9:00 AM

    # Friend data: name, location, availability start, availability end, required duration
    friends = [
        ('Mary', 'Golden Gate Park', time_to_minutes('8:45AM'), time_to_minutes('11:45AM'), 45),
        ('Kevin', 'Haight-Ashbury', time_to_minutes('10:15AM'), time_to_minutes('4:15PM'), 90),
        ('Deborah', 'Bayview', time_to_minutes('3:00PM'), time_to_minutes('7:15PM'), 120),
        ('Stephanie', 'Presidio', time_to_minutes('10:00AM'), time_to_minutes('5:15PM'), 120),
        ('Emily', 'Financial District', time_to_minutes('11:30AM'), time_to_minutes('9:45PM'), 105)
    ]

    # Initialize Z3 solver and variables
    solver = Optimize()
    n = len(friends)
    met = [Bool(f'met_{i}') for i in range(n)]
    start = [Int(f'start_{i}') for i in range(n)]
    end = [Int(f'end_{i}') for i in range(n)]
    order = [Int(f'order_{i}') for i in range(n)]

    # Constraints for each friend
    for i, (name, loc, avail_start, avail_end, dur) in enumerate(friends):
        solver.add(Implies(met[i], start[i] >= max(avail_start, 0)))  # Cannot start before 9:00
        solver.add(Implies(met[i], end[i] <= avail_end))
        solver.add(Implies(met[i], end[i] - start[i] >= dur))
        solver.add(Implies(met[i], start[i] >= 0))
        solver.add(Implies(met[i], order[i] >= 0))

    # All meetings that are met have unique order indices
    solver.add(Distinct([If(met[i], order[i], -1) for i in range(n)]))

    # Travel constraints between meetings
    for i in range(n):
        for j in range(n):
            if i != j:
                # If both meetings are scheduled and i comes immediately before j
                travel_time = travel_times[friends[i][1]][friends[j][1]]
                solver.add(Implies(And(met[i], met[j], order[i] + 1 == order[j]),
                                 start[j] >= end[i] + travel_time))

    # First meeting must account for travel from Embarcadero
    for i in range(n):
        travel_time = travel_times['Embarcadero'][friends[i][1]]
        solver.add(Implies(And(met[i], order[i] == 0), start[i] >= travel_time))

    # Maximize the number of meetings
    solver.maximize(Sum([If(met[i], 1, 0) for i in range(n)]))

    # Check satisfiability
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(n):
            if is_true(model.eval(met[i])):
                s = model.eval(start[i]).as_long()
                e = model.eval(end[i]).as_long()
                # Convert minutes back to time strings
                def minutes_to_time(m):
                    total_minutes = 540 + m  # 9:00 AM base
                    hours = total_minutes // 60
                    minutes = total_minutes % 60
                    return f"{hours}:{minutes:02d}"
                start_str = minutes_to_time(s)
                end_str = minutes_to_time(e)
                itinerary.append({
                    'action': 'meet',
                    'location': friends[i][1],
                    'person': friends[i][0],
                    'start_time': start_str,
                    'end_time': end_str
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()