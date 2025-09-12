import z3
import json

def main():
    # Define the people data
    people = [
        {
            'name': 'Helen',
            'location': 'North Beach',
            'availability_start': 540,  # 9:00 AM
            'availability_end': 1020,   # 5:00 PM
            'duration': 15
        },
        {
            'name': 'Kevin',
            'location': 'Mission District',
            'availability_start': 645,  # 10:45 AM
            'availability_end': 885,   # 2:45 PM
            'duration': 45
        },
        {
            'name': 'Amanda',
            'location': 'Alamo Square',
            'availability_start': 1185, # 7:45 PM
            'availability_end': 1260,  # 9:00 PM
            'duration': 60
        },
        {
            'name': 'Betty',
            'location': 'Financial District',
            'availability_start': 1140, # 7:00 PM
            'availability_end': 1425,  # 9:45 PM
            'duration': 90
        }
    ]

    # Define travel times between locations
    travel_times = {
        'Pacific Heights': {
            'North Beach': 9,
            'Financial District': 13,
            'Alamo Square': 10,
            'Mission District': 15
        },
        'North Beach': {
            'Pacific Heights': 8,
            'Financial District': 8,
            'Alamo Square': 16,
            'Mission District': 18
        },
        'Financial District': {
            'Pacific Heights': 13,
            'North Beach': 7,
            'Alamo Square': 17,
            'Mission District': 17
        },
        'Alamo Square': {
            'Pacific Heights': 10,
            'North Beach': 15,
            'Financial District': 17,
            'Mission District': 10
        },
        'Mission District': {
            'Pacific Heights': 16,
            'North Beach': 17,
            'Financial District': 17,
            'Alamo Square': 11
        }
    }

    # Precompute travel_between matrix for the four people's locations
    people_locations = [
        'North Beach',
        'Mission District',
        'Alamo Square',
        'Financial District'
    ]
    travel_between = [[0 for _ in range(4)] for _ in range(4)]
    for i in range(4):
        loc_i = people_locations[i]
        for j in range(4):
            loc_j = people_locations[j]
            travel_between[i][j] = travel_times[loc_i][loc_j]

    # Create Z3 variables
    solver = z3.Optimize()

    person = [z3.Int(f'person_{i}') for i in range(4)]
    start = [z3.Int(f'start_{i}') for i in range(4)]
    end = [z3.Int(f'end_{i}') for i in range(4)]

    # Add constraints for each event
    for i in range(4):
        p = person[i]
        # availability_start for the person
        avail_start = z3.If(p == 0, 540,
                z3.If(p == 1, 645,
                z3.If(p == 2, 1185,
                z3.If(p == 3, 1140, 0))))
        # availability_end
        avail_end = z3.If(p == 0, 1020,
                z3.If(p == 1, 885,
                z3.If(p == 2, 1260,
                z3.If(p == 3, 1425, 0))))
        # duration
        dur = z3.If(p == 0, 15,
                z3.If(p == 1, 45,
                z3.If(p == 2, 60,
                z3.If(p == 3, 90, 0))))
        # constraints for availability
        solver.add(z3.Implies(p != -1, z3.And(start[i] >= avail_start, start[i] + dur <= avail_end)))
        # end[i] = start[i] + duration
        solver.add(end[i] == start[i] + dur)

    # First event: travel from Pacific Heights to the location
    p = person[0]
    travel_start = z3.If(p == 0, 9,
            z3.If(p == 1, 15,
            z3.If(p == 2, 10,
            z3.If(p == 3, 13, 0))))
    solver.add(z3.Implies(p != -1, start[0] >= 540 + travel_start))

    # Constraints for consecutive events
    for i in range(1, 4):
        prev_p = person[i-1]
        curr_p = person[i]
        # travel time between prev_p and curr_p
        travel_expr = z3.If(prev_p == 0,
            z3.If(curr_p == 0, 0,
                z3.If(curr_p == 1, 18,
                    z3.If(curr_p == 2, 16,
                        z3.If(curr_p == 3, 8, 0)))),
            z3.If(prev_p == 1,
                z3.If(curr_p == 0, 17,
                    z3.If(curr_p == 1, 0,
                        z3.If(curr_p == 2, 11,
                            z3.If(curr_p == 3, 17, 0)))),
                z3.If(prev_p == 2,
                    z3.If(curr_p == 0, 15,
                        z3.If(curr_p == 1, 10,
                            z3.If(curr_p == 2, 0,
                                z3.If(curr_p == 3, 17, 0)))),
                    z3.If(prev_p == 3,
                        z3.If(curr_p == 0, 7,
                            z3.If(curr_p == 1, 17,
                                z3.If(curr_p == 2, 17,
                                    z3.If(curr_p == 3, 0, 0)))),
                        0))))
        solver.add(z3.Implies(z3.And(prev_p != -1, curr_p != -1), start[i] >= end[i-1] + travel_expr))

    # Ensure all persons are unique
    for i in range(4):
        for j in range(i+1, 4):
            solver.add(z3.Implies(z3.And(person[i] != -1, person[j] != -1), person[i] != person[j]))

    # Maximize the number of met friends
    count = z3.Sum([z3.If(person[i] != -1, 1, 0) for i in range(4)])
    solver.maximize(count)

    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        # Extract the itinerary
        itinerary = []
        for i in range(4):
            p_val = model.eval(person[i])
            if p_val.as_string() != '-1':
                p_index = int(p_val.as_string())
                start_val = model.eval(start[i]).as_long()
                end_val = model.eval(end[i]).as_long()
                person_name = people[p_index]['name']
                # Convert start and end times to H:MM format
                def to_time_str(minutes):
                    hours = minutes // 60
                    mins = minutes % 60
                    return f"{hours}:{mins:02d}"
                itinerary.append({
                    "action": "meet",
                    "location": people[p_index]['location'],
                    "person": person_name,
                    "start_time": to_time_str(start_val),
                    "end_time": to_time_str(end_val)
                })
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()