from z3 import *
import json

def main():
    # Define the friends and their attributes
    friends = ['Ronald', 'Helen', 'Joshua', 'Margaret']
    
    locations = {
        'Ronald': 'Nob Hill',
        'Helen': 'The Castro',
        'Joshua': 'Sunset District',
        'Margaret': 'Haight-Ashbury'
    }
    
    durations = {
        'Ronald': 105,
        'Helen': 120,
        'Joshua': 90,
        'Margaret': 60
    }
    
    availability_start = {
        'Ronald': 60,    # 10:00
        'Helen': 270,    # 13:30
        'Joshua': 315,   # 14:15
        'Margaret': 75    # 10:15
    }
    
    availability_end = {
        'Ronald': 480,   # 17:00
        'Helen': 480,    # 17:00
        'Joshua': 630,   # 19:30
        'Margaret': 780   # 22:00
    }
    
    # Travel times dictionary - as given
    travel_times = {
        "Pacific Heights": {
            "Nob Hill": 8,
            "Russian Hill": 7,
            "The Castro": 16,
            "Sunset District": 21,
            "Haight-Ashbury": 11
        },
        "Nob Hill": {
            "Pacific Heights": 8,
            "Russian Hill": 5,
            "The Castro": 17,
            "Sunset District": 25,
            "Haight-Ashbury": 13
        },
        "Russian Hill": {
            "Pacific Heights": 7,
            "Nob Hill": 5,
            "The Castro": 21,
            "Sunset District": 23,
            "Haight-Ashbury": 17
        },
        "The Castro": {
            "Pacific Heights": 16,
            "Nob Hill": 16,
            "Russian Hill": 18,
            "Sunset District": 17,
            "Haight-Ashbury": 6
        },
        "Sunset District": {
            "Pacific Heights": 21,
            "Nob Hill": 27,
            "Russian Hill": 24,
            "The Castro": 17,
            "Haight-Ashbury": 15
        },
        "Haight-Ashbury": {
            "Pacific Heights": 12,
            "Nob Hill": 15,
            "Russian Hill": 17,
            "The Castro": 6,
            "Sunset District": 15
        }
    }

    # Create Z3 variables for start times: one for each friend
    S = {}
    for friend in friends:
        S[friend] = Int(f'S_{friend}')

    # Create booleans for every pair (i, j) with i < j in the index of the friends list
    n = len(friends)
    B = {}  # Key: (i,j) for i<j
    pairs = []
    for i in range(n):
        for j in range(i+1, n):
            key = (i, j)
            B[key] = Bool(f'B_{i}_{j}')
            pairs.append(key)

    solver = Solver()

    # Constraint 1: availability constraints and travel from start
    for friend in friends:
        loc = locations[friend]
        # Travel time from Pacific Heights to this location
        travel_from_start = travel_times['Pacific Heights'][loc]
        solver.add(S[friend] >= availability_start[friend])
        solver.add(S[friend] <= availability_end[friend] - durations[friend])
        solver.add(S[friend] >= travel_from_start)

    # Constraint 2: for every pair (i,j) with i<j
    for (i, j) in pairs:
        friend_i = friends[i]
        friend_j = friends[j]
        loc_i = locations[friend_i]
        loc_j = locations[friend_j]
        travel_ij = travel_times[loc_i][loc_j]
        travel_ji = travel_times[loc_j][loc_i]
        cond1 = (S[friend_j] >= S[friend_i] + durations[friend_i] + travel_ij)
        cond2 = (S[friend_i] >= S[friend_j] + durations[friend_j] + travel_ji)
        solver.add(If(B[(i, j)], cond1, cond2))

    if solver.check() == sat:
        model = solver.model()
        meeting_list = []
        for friend in friends:
            start_val = model.evaluate(S[friend]).as_long()
            end_val = start_val + durations[friend]
            total_minutes_start = start_val
            hours_start = 9 + total_minutes_start // 60
            minutes_start = total_minutes_start % 60
            start_str = f"{hours_start:02d}:{minutes_start:02d}"

            total_minutes_end = end_val
            hours_end = 9 + total_minutes_end // 60
            minutes_end = total_minutes_end % 60
            end_str = f"{hours_end:02d}:{minutes_end:02d}"

            meeting_list.append({
                "action": "meet",
                "person": friend,
                "start_time": start_str,
                "end_time": end_str
            })

        meeting_list.sort(key=lambda x: x['start_time'])
        result = {"itinerary": meeting_list}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()