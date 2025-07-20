from z3 import *
import json

def main():
    # Define friends data: name, location, (available_start, available_end) in minutes, min_duration
    friends = [
        ("Laura", "The Castro", (19*60+45, 21*60+30), 105),   # 7:45 PM to 9:30 PM
        ("Daniel", "Golden Gate Park", (21*60+15, 21*60+45), 15), # 9:15 PM to 9:45 PM
        ("William", "Embarcadero", (7*60, 9*60), 90),          # 7:00 AM to 9:00 AM
        ("Karen", "Russian Hill", (14*60+30, 19*60+45), 30),   # 2:30 PM to 7:45 PM
        ("Stephanie", "Nob Hill", (7*60+30, 9*60+30), 45),     # 7:30 AM to 9:30 AM
        ("Joseph", "Alamo Square", (11*60+30, 12*60+45), 15),  # 11:30 AM to 12:45 PM
        ("Kimberly", "North Beach", (15*60+45, 19*60+15), 30)  # 3:45 PM to 7:15 PM
    ]
    base_time = 9 * 60  # 9:00 AM in minutes

    # Build travel dictionary
    travel_dict = {
        ("Fisherman's Wharf", "The Castro"): 26,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Alamo Square"): 20,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "North Beach"): 20,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "North Beach"): 24,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "North Beach"): 5,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "North Beach"): 5,
        ("Nob Hill", "Fisherman's Wharf"): 11,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "North Beach"): 8,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Embarcadero"): 17,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "North Beach"): 15,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "The Castro"): 22,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Alamo Square"): 16
    }

    n = len(friends)
    # Create Z3 variables
    meet = [Bool(f"meet_{i}") for i in range(n)]
    start = [Int(f"start_{i}") for i in range(n)]
    end = [Int(f"end_{i}") for i in range(n)]
    
    # Create before matrix: before[i][j] is True if meeting i is before meeting j
    before = [[Bool(f"before_{i}_{j}") if i != j else None for j in range(n)] for i in range(n)]
    
    solver = Optimize()
    
    # Set William (index 2) and Stephanie (index 4) to not meet
    solver.add(meet[2] == False)
    solver.add(meet[4] == False)
    
    # Constraints for each friend
    for i in range(n):
        name, loc, (avail_start, avail_end), min_dur = friends[i]
        # If we meet this friend, the meeting must be within their availability and last at least min_dur
        solver.add(Implies(meet[i], start[i] >= avail_start))
        solver.add(Implies(meet[i], end[i] <= avail_end))
        solver.add(Implies(meet[i], end[i] - start[i] >= min_dur))
    
    # Travel time from base to each friend's location
    T_base = {}
    for i in range(n):
        name, loc, _, _ = friends[i]
        T_base[i] = travel_dict[("Fisherman's Wharf", loc)]
    
    # Travel time between friends
    T = {}
    for i in range(n):
        name_i, loc_i, _, _ = friends[i]
        for j in range(n):
            if i == j:
                continue
            name_j, loc_j, _, _ = friends[j]
            T[(i, j)] = travel_dict[(loc_i, loc_j)]
    
    # Ordering constraints: for every pair of distinct friends we might meet
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            # If both i and j are met, then either i before j or j before i, but not both
            solver.add(Implies(And(meet[i], meet[j]), Or(before[i][j], before[j][i])))
            solver.add(Implies(And(meet[i], meet[j]), Not(And(before[i][j], before[j][i]))))
    
    # Constraints for the start time of each meeting
    for i in range(n):
        name, loc, _, _ = friends[i]
        # Define first_i: no other meeting j is before i
        first_i = And(meet[i], *[Not(before[j][i]) for j in range(n) if j != i])
        # If the meeting i is the first, then start_i >= base_time + T_base[i]
        # Otherwise, there exists a meeting j that is before i, and start_i >= end_j + T[j][i]
        other_conditions = []
        for j in range(n):
            if j == i:
                continue
            cond = And(before[j][i], start[i] >= end[j] + T[(j, i)])
            other_conditions.append(cond)
        solver.add(Implies(meet[i], 
                    If(first_i, 
                       start[i] >= base_time + T_base[i],
                       Or(other_conditions)
                    )))
    
    # Maximize the number of meetings
    solver.maximize(Sum([If(meet[i], 1, 0) for i in range(n)]))
    
    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        meetings_list = []
        for i in range(n):
            if is_true(model.eval(meet[i])):
                s_val = model.eval(start[i]).as_long()
                e_val = model.eval(end[i]).as_long()
                s_hour = s_val // 60
                s_min = s_val % 60
                e_hour = e_val // 60
                e_min = e_val % 60
                start_str = f"{s_hour:02d}:{s_min:02d}"
                end_str = f"{e_hour:02d}:{e_min:02d}"
                name = friends[i][0]
                meetings_list.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_str,
                    "end_time": end_str
                })
        
        # Define key function for sorting
        def get_key(meeting):
            parts = meeting['start_time'].split(':')
            hour = int(parts[0])
            minute = int(parts[1])
            return (hour, minute)
        
        # Sort meetings by start time
        meetings_list.sort(key=get_key)
        result = {"itinerary": meetings_list}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()