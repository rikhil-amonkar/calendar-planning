import json
from z3 import *

def time_to_minutes(t):
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Travel times dictionary
    travel_times = {
        'Pacific Heights': {
            'Marina District': 6,
            'The Castro': 16,
            'Richmond District': 12,
            'Alamo Square': 10,
            'Financial District': 13,
            'Presidio': 11,
            'Mission District': 15,
            'Nob Hill': 8,
            'Russian Hill': 7
        },
        'Marina District': {
            'Pacific Heights': 7,
            'The Castro': 22,
            'Richmond District': 11,
            'Alamo Square': 15,
            'Financial District': 17,
            'Presidio': 10,
            'Mission District': 20,
            'Nob Hill': 12,
            'Russian Hill': 8
        },
        'The Castro': {
            'Pacific Heights': 16,
            'Marina District': 21,
            'Richmond District': 16,
            'Alamo Square': 8,
            'Financial District': 21,
            'Presidio': 20,
            'Mission District': 7,
            'Nob Hill': 16,
            'Russian Hill': 18
        },
        'Richmond District': {
            'Pacific Heights': 10,
            'Marina District': 9,
            'The Castro': 16,
            'Alamo Square': 13,
            'Financial District': 22,
            'Presidio': 7,
            'Mission District': 20,
            'Nob Hill': 17,
            'Russian Hill': 13
        },
        'Alamo Square': {
            'Pacific Heights': 10,
            'Marina District': 15,
            'The Castro': 8,
            'Richmond District': 11,
            'Financial District': 17,
            'Presidio': 17,
            'Mission District': 10,
            'Nob Hill': 11,
            'Russian Hill': 13
        },
        'Financial District': {
            'Pacific Heights': 13,
            'Marina District': 15,
            'The Castro': 20,
            'Richmond District': 21,
            'Alamo Square': 17,
            'Presidio': 22,
            'Mission District': 17,
            'Nob Hill': 8,
            'Russian Hill': 11
        },
        'Presidio': {
            'Pacific Heights': 11,
            'Marina District': 11,
            'The Castro': 21,
            'Richmond District': 7,
            'Alamo Square': 19,
            'Financial District': 23,
            'Mission District': 26,
            'Nob Hill': 18,
            'Russian Hill': 14
        },
        'Mission District': {
            'Pacific Heights': 16,
            'Marina District': 19,
            'The Castro': 7,
            'Richmond District': 20,
            'Alamo Square': 11,
            'Financial District': 15,
            'Presidio': 25,
            'Nob Hill': 12,
            'Russian Hill': 15
        },
        'Nob Hill': {
            'Pacific Heights': 8,
            'Marina District': 11,
            'The Castro': 17,
            'Richmond District': 14,
            'Alamo Square': 11,
            'Financial District': 9,
            'Presidio': 17,
            'Mission District': 13,
            'Russian Hill': 5
        },
        'Russian Hill': {
            'Pacific Heights': 7,
            'Marina District': 7,
            'The Castro': 21,
            'Richmond District': 14,
            'Alamo Square': 15,
            'Financial District': 11,
            'Presidio': 14,
            'Mission District': 16,
            'Nob Hill': 5
        }
    }

    # Friend constraints
    friends = [
        {'name': 'Linda', 'location': 'Marina District', 'start_window': time_to_minutes('18:00'), 'end_window': time_to_minutes('22:00'), 'min_duration': 30},
        {'name': 'Kenneth', 'location': 'The Castro', 'start_window': time_to_minutes('14:45'), 'end_window': time_to_minutes('16:15'), 'min_duration': 30},
        {'name': 'Kimberly', 'location': 'Richmond District', 'start_window': time_to_minutes('14:15'), 'end_window': time_to_minutes('22:00'), 'min_duration': 30},
        {'name': 'Paul', 'location': 'Alamo Square', 'start_window': time_to_minutes('21:00'), 'end_window': time_to_minutes('21:30'), 'min_duration': 15},
        {'name': 'Carol', 'location': 'Financial District', 'start_window': time_to_minutes('10:15'), 'end_window': time_to_minutes('12:00'), 'min_duration': 60},
        {'name': 'Brian', 'location': 'Presidio', 'start_window': time_to_minutes('10:00'), 'end_window': time_to_minutes('21:30'), 'min_duration': 75},
        {'name': 'Laura', 'location': 'Mission District', 'start_window': time_to_minutes('16:15'), 'end_window': time_to_minutes('20:30'), 'min_duration': 30},
        {'name': 'Sandra', 'location': 'Nob Hill', 'start_window': time_to_minutes('9:15'), 'end_window': time_to_minutes('18:30'), 'min_duration': 60},
        {'name': 'Karen', 'location': 'Russian Hill', 'start_window': time_to_minutes('18:30'), 'end_window': time_to_minutes('22:00'), 'min_duration': 75}
    ]

    # Initialize solver
    opt = Optimize()
    n = len(friends)

    # Meeting decision variables
    meet = [Bool(f"meet_{i}") for i in range(n)]
    start_time_vars = [Real(f"start_{i}") for i in range(n)]
    end_time_vars = [Real(f"end_{i}") for i in range(n)]

    # Start at Pacific Heights at 9:00 (0 minutes)
    current_location = 'Pacific Heights'
    current_time = 0

    # Constraints for each friend
    for i, f in enumerate(friends):
        # If we meet, constraints on time window and duration
        opt.add(Implies(meet[i], start_time_vars[i] >= f['start_window']))
        opt.add(Implies(meet[i], end_time_vars[i] == start_time_vars[i] + f['min_duration']))
        opt.add(Implies(meet[i], end_time_vars[i] <= f['end_window']))

    # Constraints for travel between meetings
    for i in range(n):
        for j in range(n):
            if i != j:
                # Travel from meeting i to meeting j
                travel_ij = travel_times[friends[i]['location']][friends[j]['location']]
                opt.add(Implies(And(meet[i], meet[j]),
                    Or(
                        end_time_vars[i] + travel_ij <= start_time_vars[j],
                        end_time_vars[j] + travel_ij <= start_time_vars[i]
                    )))

        # Travel from current location to first meeting
        travel_start = travel_times[current_location][friends[i]['location']]
        opt.add(Implies(meet[i], start_time_vars[i] >= current_time + travel_start))

    # Maximize number of meetings
    opt.maximize(Sum([If(meet[i], 1, 0) for i in range(n)]))

    # Check and get model
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        meeting_times = []
        for i, f in enumerate(friends):
            if is_true(model.eval(meet[i])):
                start_val = model.eval(start_time_vars[i])
                end_val = model.eval(end_time_vars[i])
                if isinstance(start_val, ArithRef) or isinstance(end_val, ArithRef):
                    continue
                start_minutes = int(start_val.as_string())
                end_minutes = int(end_val.as_string())
                meeting_times.append((f['name'], f['location'], start_minutes, end_minutes))
        
        # Sort meetings by start time
        meeting_times.sort(key=lambda x: x[2])
        itinerary = [
            {
                "action": "meet",
                "location": loc,
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            }
            for name, loc, start, end in meeting_times
        ]
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()