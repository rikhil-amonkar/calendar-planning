import z3
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def get_location_name(loc_idx):
    locations = ["Golden Gate Park", "Haight-Ashbury", "Sunset District", "Marina District", "Financial District", "Union Square"]
    return locations[loc_idx]

def main():
    # Define friends' data: (name, availability_start, availability_end, duration)
    friends_data = [
        ("Matthew", 555, 720, 15),          # 9:15 AM to 12:00 PM, 15 min
        ("Robert", 615, 1305, 15),          # 10:15 AM to 9:45 PM, 15 min
        ("Joseph", 855, 1125, 30),         # 2:15 PM to 6:45 PM, 30 min
        ("Sarah", 1020, 1290, 105),        # 5:00 PM to 9:30 PM, 105 min
        ("Patricia", 1020, 1185, 45)       # 5:00 PM to 7:45 PM, 45 min
    ]
    friend_names = [f[0] for f in friends_data]
    friend_to_location = [3, 5, 4, 1, 2]  # Matthew at Marina (3), Robert at Union (5), etc.

    # Travel time matrix: [from][to]
    travel_time = [
        [0, 7, 10, 16, 26, 22],  # GGP to each
        [7, 0, 15, 17, 21, 17],  # Haight
        [11, 15, 0, 21, 30, 30], # Sunset
        [18, 16, 19, 0, 17, 16], # Marina
        [23, 19, 31, 15, 0, 9],  # Financial
        [22, 18, 26, 18, 9, 0]   # Union
    ]

    # Z3 solver setup
    opt = z3.Optimize()

    # Maximum number of positions in the itinerary
    positions = 5
    friends = [z3.Int(f'friend_{i}') for i in range(positions)]
    starts = [z3.Int(f'start_{i}') for i in range(positions)]
    ends = [z3.Int(f'end_{i}') for i in range(positions)]

    # Constraints: each friend is scheduled at most once
    for i in range(positions):
        for j in range(i + 1, positions):
            opt.add(z3.Or(friends[i] == -1, friends[j] == -1, friends[i] != friends[j]))

    # Constraints: for each position, if not -1, then start and end times are valid
    for i in range(positions):
        for friend_idx in range(5):
            # If friends[i] == friend_idx, then apply constraints
            start_min = friends_data[friend_idx][1]
            end_min = friends_data[friend_idx][2]
            duration = friends_data[friend_idx][3]
            opt.add(z3.Implies(
                friends[i] == friend_idx,
                z3.And(
                    starts[i] >= start_min,
                    ends[i] <= end_min,
                    ends[i] - starts[i] >= duration
                )
            ))

    # Constraints: friends[i] must be -1 or 0-4
    for i in range(positions):
        opt.add(z3.Or(friends[i] == -1, *[friends[i] == idx for idx in range(5)]))

    # Constraints: first position's start time must account for travel from GGP
    for friend_idx in range(5):
        loc_idx = friend_to_location[friend_idx]
        travel = travel_time[0][loc_idx]  # from GGP (0) to loc_idx
        opt.add(z3.Implies(
            friends[0] == friend_idx,
            starts[0] >= 540 + travel  # arrival at GGP is 9:00 AM = 540 min
        ))

    # Constraints: consecutive positions
    for i in range(positions - 1):
        for friend_i in range(5):
            for friend_j in range(5):
                loc_i = friend_to_location[friend_i]
                loc_j = friend_to_location[friend_j]
                travel = travel_time[loc_i][loc_j]
                opt.add(z3.Implies(
                    z3.And(friends[i] == friend_i, friends[i+1] == friend_j),
                    starts[i+1] >= ends[i] + travel
                ))

    # Objective: maximize the number of friends met
    count = z3.Sum([z3.If(friends[i] != -1, 1, 0) for i in range(positions)])
    opt.maximize(count)

    # Check if the problem is satisfiable
    if opt.check() == z3.sat:
        model = opt.model()
        itinerary = []
        for i in range(positions):
            friend_idx = model.evaluate(friends[i]).as_long()
            if friend_idx != -1:
                start = model.evaluate(starts[i]).as_long()
                end = model.evaluate(ends[i]).as_long()
                name = friend_names[friend_idx]
                loc_idx = friend_to_location[friend_idx]
                location_name = get_location_name(loc_idx)
                start_time = minutes_to_time(start)
                end_time = minutes_to_time(end)
                itinerary.append({
                    "action": "meet",
                    "location": location_name,
                    "person": name,
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Sort the itinerary by start time (should already be in order)
        itinerary.sort(key=lambda x: x['start_time'])
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()