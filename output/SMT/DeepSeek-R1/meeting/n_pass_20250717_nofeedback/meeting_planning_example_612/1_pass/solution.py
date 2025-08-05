from z3 import *
import json

def main():
    # Total meetings: start (0) and 7 friends (1 to 7)
    n_friends = 7
    total_meetings = n_friends + 1  # including start

    # Friend data: index from 1 to 7 (0 is start)
    names = {
        1: "Emily", 
        2: "Mark", 
        3: "Deborah", 
        4: "Margaret", 
        5: "George", 
        6: "Andrew", 
        7: "Steven"
    }

    # Locations indices:
    # 0: Alamo Square, 1: Russian Hill, 2: Presidio, 3: Chinatown, 4: Sunset District, 5: The Castro, 6: Embarcadero, 7: Golden Gate Park
    # Travel time matrix T: 8x8, T[i][j] = time from location i to j
    T = [
        [0, 13, 18, 16, 16, 8, 17, 9],
        [15, 0, 14, 9, 23, 21, 8, 21],
        [18, 14, 0, 21, 15, 21, 20, 12],
        [17, 7, 19, 0, 29, 22, 5, 23],
        [17, 24, 16, 30, 0, 17, 31, 11],
        [8, 18, 20, 20, 17, 0, 22, 11],
        [19, 8, 20, 7, 30, 25, 0, 25],
        [10, 19, 11, 23, 10, 13, 25, 0]
    ]

    # Availability and durations for friends 1..7 (in minutes from midnight)
    avail_start = {
        1: 12*60 + 15,   # 12:15PM
        2: 14*60 + 45,    # 2:45PM
        3: 7*60 + 30,     # 7:30AM
        4: 21*60 + 30,    # 9:30PM
        5: 7*60 + 30,     # 7:30AM
        6: 20*60 + 15,    # 8:15PM
        7: 11*60 + 15     # 11:15AM
    }
    avail_end = {
        1: 14*60 + 15,   # 2:15PM
        2: 19*60 + 30,    # 7:30PM
        3: 15*60 + 30,    # 3:30PM
        4: 22*60 + 30,    # 10:30PM
        5: 14*60 + 15,    # 2:15PM
        6: 22*60 + 0,     # 10:00PM
        7: 21*60 + 15     # 9:15PM
    }
    min_duration = {
        1: 105,
        2: 60,
        3: 45,
        4: 60,
        5: 60,
        6: 75,
        7: 105
    }

    # Z3 variables
    meet = [Bool(f'meet_{i}') for i in range(1, 8)]  # meet_i for friend i (index 1..7)
    start_time = [Int(f'start_{i}') for i in range(0, 8)]  # start_time for meeting i (0..7)
    end_time = [Int(f'end_{i}') for i in range(0, 8)]      # end_time for meeting i (0..7)
    before = [[Bool(f'before_{i}_{j}') for j in range(8)] for i in range(8)]  # before[i][j] for i,j in 0..7

    solver = Solver()

    # Meeting 0 (start at Alamo Square) is fixed
    solver.add(start_time[0] == 540)  # 9:00AM
    solver.add(end_time[0] == 540)

    # Constraints for friends 1..7: if meet_i is True, then meeting must be within availability window
    for i in range(1, 8):
        solver.add(Implies(meet[i-1], 
                           And(start_time[i] >= avail_start[i],
                               end_time[i] == start_time[i] + min_duration[i],
                               end_time[i] <= avail_end[i]
                           )))

    # For any friend j that is met, the start (0) must be before j
    for j in range(1, 8):
        solver.add(Implies(meet[j-1], before[0][j]))

    # For every distinct pair (i, j): if both meetings are selected, enforce ordering and travel time
    for i in range(8):
        for j in range(8):
            if i == j:
                continue
            # Determine if meetings i and j are selected
            selected_i = meet[i-1] if i >= 1 else BoolVal(True)
            selected_j = meet[j-1] if j >= 1 else BoolVal(True)
            both_selected = And(selected_i, selected_j)

            # If both selected, enforce travel time constraints and mutual exclusivity of before[i][j] and before[j][i]
            constraint1 = Implies(before[i][j], end_time[i] + T[i][j] <= start_time[j])
            constraint2 = Implies(before[j][i], end_time[j] + T[j][i] <= start_time[i])
            constraint3 = Or(before[i][j], before[j][i])
            constraint4 = Not(And(before[i][j], before[j][i]))
            solver.add(Implies(both_selected, And(constraint1, constraint2, constraint3, constraint4)))

    # Transitivity: for every distinct i, j, k, if all selected, then before[i][j] and before[j][k] implies before[i][k]
    for i in range(8):
        for j in range(8):
            if i == j:
                continue
            for k in range(8):
                if i == k or j == k:
                    continue
                selected_i = meet[i-1] if i >= 1 else BoolVal(True)
                selected_j = meet[j-1] if j >= 1 else BoolVal(True)
                selected_k = meet[k-1] if k >= 1 else BoolVal(True)
                all_selected = And(selected_i, selected_j, selected_k)
                trans = Implies(And(before[i][j], before[j][k]), before[i][k])
                solver.add(Implies(all_selected, trans))

    # Optimize to maximize the number of friends met
    opt = Optimize()
    opt.add(solver.assertions())
    objective = Sum([If(meet_i, 1, 0) for meet_i in meet])
    opt.maximize(objective)

    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for i in range(1, 8):
            if model.evaluate(meet[i-1]):
                start_val = model.evaluate(start_time[i])
                end_val = model.evaluate(end_time[i])
                start_min = start_val.as_long()
                end_min = end_val.as_long()
                start_hh = start_min // 60
                start_mm = start_min % 60
                end_hh = end_min // 60
                end_mm = end_min % 60
                start_str = f"{start_hh:02d}:{start_mm:02d}"
                end_str = f"{end_hh:02d}:{end_mm:02d}"
                scheduled_meetings.append({
                    "action": "meet",
                    "person": names[i],
                    "start_time": start_str,
                    "end_time": end_str
                })
        
        # Sort meetings by start time
        scheduled_meetings.sort(key=lambda x: x['start_time'])
        
        # Output the solution
        print("SOLUTION:")
        output = {"itinerary": scheduled_meetings}
        print(json.dumps(output))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()