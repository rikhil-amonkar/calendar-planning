from z3 import *

def main():
    # Define friends and their constraints
    friends = [
        {'name': 'Robert', 'loc': 'Nob Hill', 'start_avail': 465, 'end_avail': 630, 'dur': 90},
        {'name': 'Steven', 'loc': 'Golden Gate Park', 'start_avail': 510, 'end_avail': 1020, 'dur': 75},
        {'name': 'Anthony', 'loc': 'Alamo Square', 'start_avail': 465, 'end_avail': 1185, 'dur': 15},
        {'name': 'Sandra', 'loc': 'Pacific Heights', 'start_avail': 885, 'end_avail': 1305, 'dur': 45},
        {'name': 'Kevin', 'loc': 'Fisherman\'s Wharf', 'start_avail': 1155, 'end_avail': 1305, 'dur': 75},
        {'name': 'Stephanie', 'loc': 'Russian Hill', 'start_avail': 1200, 'end_avail': 1245, 'dur': 15}
    ]
    
    # Map index to friend name
    index_to_friend = {i: friends[i]['name'] for i in range(6)}
    
    # Travel times between locations (in minutes)
    travel_times = {
        'Haight-Ashbury': {
            'Russian Hill': 17,
            'Fisherman\'s Wharf': 23,
            'Nob Hill': 15,
            'Golden Gate Park': 7,
            'Alamo Square': 5,
            'Pacific Heights': 12
        },
        'Russian Hill': {
            'Haight-Ashbury': 17,
            'Fisherman\'s Wharf': 7,
            'Nob Hill': 5,
            'Golden Gate Park': 21,
            'Alamo Square': 15,
            'Pacific Heights': 7
        },
        'Fisherman\'s Wharf': {
            'Haight-Ashbury': 22,
            'Russian Hill': 7,
            'Nob Hill': 11,
            'Golden Gate Park': 25,
            'Alamo Square': 20,
            'Pacific Heights': 12
        },
        'Nob Hill': {
            'Haight-Ashbury': 13,
            'Russian Hill': 5,
            'Fisherman\'s Wharf': 11,
            'Golden Gate Park': 17,
            'Alamo Square': 11,
            'Pacific Heights': 8
        },
        'Golden Gate Park': {
            'Haight-Ashbury': 7,
            'Russian Hill': 19,
            'Fisherman\'s Wharf': 24,
            'Nob Hill': 20,
            'Alamo Square': 10,
            'Pacific Heights': 16
        },
        'Alamo Square': {
            'Haight-Ashbury': 5,
            'Russian Hill': 13,
            'Fisherman\'s Wharf': 19,
            'Nob Hill': 11,
            'Golden Gate Park': 9,
            'Pacific Heights': 10
        },
        'Pacific Heights': {
            'Haight-Ashbury': 11,
            'Russian Hill': 7,
            'Fisherman\'s Wharf': 13,
            'Nob Hill': 8,
            'Golden Gate Park': 15,
            'Alamo Square': 10
        }
    }
    
    # Initialize Z3 variables and solver
    s = Solver()
    opt = Optimize()
    n_slots = 6
    slot = [Int(f'slot_{i}') for i in range(n_slots)]
    start = [Int(f'start_{i}') for i in range(n_slots)]
    end = [Int(f'end_{i}') for i in range(n_slots)]
    
    # Slot constraints: each slot is between 0 and 5 (friend) or 6 (none)
    for i in range(n_slots):
        opt.add(Or(And(slot[i] >= 0, slot[i] <= 5), slot[i] == 6))
    
    # If a slot is none, subsequent slots must be none
    for i in range(n_slots - 1):
        opt.add(Implies(slot[i] == 6, slot[i+1] == 6))
    
    # Each friend is scheduled at most once
    for friend_idx in range(6):
        count = 0
        for i in range(n_slots):
            count += If(And(slot[i] >= 0, slot[i] <= 5, slot[i] == friend_idx), 1, 0)
        opt.add(count <= 1)
    
    # Define end times
    for i in range(n_slots):
        dur_i = Int(f'dur_{i}')
        # If slot[i] is a friend, set dur_i to that friend's duration; else 0
        dur_expr = 0
        for idx in range(6):
            dur_expr = If(slot[i] == idx, friends[idx]['dur'], dur_expr)
        dur_i = dur_expr
        opt.add(end[i] == If(slot[i] != 6, start[i] + dur_i, 0))
    
    # Constraints for the first slot
    for idx in range(6):
        opt.add(If(slot[0] == idx,
                   And(
                       start[0] >= 540 + travel_times['Haight-Ashbury'][friends[idx]['loc']],
                       start[0] >= friends[idx]['start_avail'],
                       end[0] <= friends[idx]['end_avail']
                   ),
                   True))
    
    # Constraints for subsequent slots
    for i in range(1, n_slots):
        for prev_idx in range(6):
            for curr_idx in range(6):
                # If slot[i-1] is prev_idx and slot[i] is curr_idx
                cond = And(slot[i-1] == prev_idx, slot[i] == curr_idx)
                loc_prev = friends[prev_idx]['loc']
                loc_curr = friends[curr_idx]['loc']
                travel_time = travel_times[loc_prev][loc_curr]
                opt.add(If(cond,
                           And(
                               start[i] >= end[i-1] + travel_time,
                               start[i] >= friends[curr_idx]['start_avail'],
                               end[i] <= friends[curr_idx]['end_avail']
                           ),
                           True))
        # Also consider the case when the previous slot is none
        opt.add(If(slot[i-1] == 6, slot[i] == 6, True))
    
    # Total meetings to maximize
    total_meetings = Sum([If(slot[i] != 6, 1, 0) for i in range(n_slots)])
    opt.maximize(total_meetings)
    
    # Solve the model
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for i in range(n_slots):
            slot_val = m[slot[i]].as_long()
            if slot_val != 6:  # A meeting is scheduled in this slot
                friend_name = index_to_friend[slot_val]
                start_val = m[start[i]].as_long()
                end_val = m[end[i]].as_long()
                # Convert minutes to HH:MM
                start_h = start_val // 60
                start_m = start_val % 60
                end_h = end_val // 60
                end_m = end_val % 60
                start_time = f"{start_h:02d}:{start_m:02d}"
                end_time = f"{end_h:02d}:{end_m:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friend_name,
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Output the itinerary as JSON
        print('SOLUTION:')
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print("No solution found")

if __name__ == '__main__':
    main()