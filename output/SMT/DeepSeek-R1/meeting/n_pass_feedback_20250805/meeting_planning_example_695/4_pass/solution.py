from z3 import *

def main():
    # Define travel times between locations
    locations = ["Bayview", "Nob Hill", "Union Square", "Chinatown", "The Castro", "Presidio", "Pacific Heights", "Russian Hill"]
    travel_time = [[0] * 8 for _ in range(8)]
    
    # Bayview to others
    travel_time[0][1] = 20  # Nob Hill
    travel_time[0][2] = 17  # Union Square
    travel_time[0][3] = 18  # Chinatown
    travel_time[0][4] = 20  # The Castro
    travel_time[0][5] = 31  # Presidio
    travel_time[0][6] = 23  # Pacific Heights
    travel_time[0][7] = 23  # Russian Hill
    
    # Nob Hill to others
    travel_time[1][0] = 19  # Bayview
    travel_time[1][2] = 7   # Union Square
    travel_time[1][3] = 6   # Chinatown
    travel_time[1][4] = 17  # The Castro
    travel_time[1][5] = 17  # Presidio
    travel_time[1][6] = 8   # Pacific Heights
    travel_time[1][7] = 5   # Russian Hill
    
    # Union Square to others
    travel_time[2][0] = 15  # Bayview
    travel_time[2][1] = 9   # Nob Hill
    travel_time[2][3] = 7   # Chinatown
    travel_time[2][4] = 19  # The Castro
    travel_time[2][5] = 24  # Presidio
    travel_time[2][6] = 15  # Pacific Heights
    travel_time[2][7] = 13  # Russian Hill
    
    # Chinatown to others
    travel_time[3][0] = 22  # Bayview
    travel_time[3][1] = 8   # Nob Hill
    travel_time[3][2] = 7   # Union Square
    travel_time[3][4] = 22  # The Castro
    travel_time[3][5] = 19  # Presidio
    travel_time[3][6] = 10  # Pacific Heights
    travel_time[3][7] = 7   # Russian Hill
    
    # The Castro to others
    travel_time[4][0] = 19  # Bayview
    travel_time[4][1] = 16  # Nob Hill
    travel_time[4][2] = 19  # Union Square
    travel_time[4][3] = 20  # Chinatown
    travel_time[4][5] = 20  # Presidio
    travel_time[4][6] = 16  # Pacific Heights
    travel_time[4][7] = 18  # Russian Hill
    
    # Presidio to others
    travel_time[5][0] = 31  # Bayview
    travel_time[5][1] = 18  # Nob Hill
    travel_time[5][2] = 22  # Union Square
    travel_time[5][3] = 21  # Chinatown
    travel_time[5][4] = 21  # The Castro
    travel_time[5][6] = 11  # Pacific Heights
    travel_time[5][7] = 14  # Russian Hill
    
    # Pacific Heights to others
    travel_time[6][0] = 22  # Bayview
    travel_time[6][1] = 8   # Nob Hill
    travel_time[6][2] = 12  # Union Square
    travel_time[6][3] = 11  # Chinatown
    travel_time[6][4] = 16  # The Castro
    travel_time[6][5] = 11  # Presidio
    travel_time[6][7] = 7   # Russian Hill
    
    # Russian Hill to others
    travel_time[7][0] = 23  # Bayview
    travel_time[7][1] = 5   # Nob Hill
    travel_time[7][2] = 11  # Union Square
    travel_time[7][3] = 9   # Chinatown
    travel_time[7][4] = 21  # The Castro
    travel_time[7][5] = 14  # Presidio
    travel_time[7][6] = 7   # Pacific Heights

    # Friends data
    friends = [
        {"name": "Paul", "location": 1, "start_win": 16*60+15, "end_win": 21*60+15, "min_dur": 60},
        {"name": "Carol", "location": 2, "start_win": 18*60, "end_win": 20*60+15, "min_dur": 120},
        {"name": "Patricia", "location": 3, "start_win": 20*60, "end_win": 21*60+30, "min_dur": 75},
        {"name": "Karen", "location": 4, "start_win": 17*60, "end_win": 19*60, "min_dur": 45},
        {"name": "Nancy", "location": 5, "start_win": 11*60+45, "end_win": 22*60, "min_dur": 30},
        {"name": "Jeffrey", "location": 6, "start_win": 20*60, "end_win": 20*60+45, "min_dur": 45},
        {"name": "Matthew", "location": 7, "start_win": 15*60+45, "end_win": 21*60+45, "min_dur": 75}
    ]

    # Use Optimize instead of Solver for maximization
    opt = Optimize()

    # Decision variables
    meet_vars = [Bool(f"meet_{i}") for i in range(7)]
    start_vars = [Int(f"start_{i}") for i in range(7)]
    end_vars = [Int(f"end_{i}") for i in range(7)]

    # Meeting constraints
    for i in range(7):
        opt.add(end_vars[i] == start_vars[i] + friends[i]["min_dur"])
        opt.add(Implies(meet_vars[i], start_vars[i] >= friends[i]["start_win"]))
        opt.add(Implies(meet_vars[i], end_vars[i] <= friends[i]["end_win"]))

    # Dummy meeting at Bayview (starting point)
    dummy_start = 9*60  # 9:00 AM in minutes
    dummy_end = 9*60
    dummy_loc = 0

    # Combine all meetings (dummy + friends)
    meet_list = [True] + meet_vars
    start_list = [dummy_start] + start_vars
    end_list = [dummy_end] + end_vars
    loc_list = [dummy_loc] + [f["location"] for f in friends]

    # Before matrix: before[i][j] means meeting i is before meeting j
    before = [[Bool(f"before_{i}_{j}") for j in range(8)] for i in range(8)]

    # Constraints for dummy meeting (must be before all others)
    for j in range(1, 8):
        opt.add(before[0][j] == meet_list[j])
        opt.add(before[j][0] == False)

    # Constraints for all meeting pairs
    for i in range(8):
        for j in range(8):
            if i == j:
                continue
                
            # Mutual exclusion for ordering
            opt.add(Implies(
                And(meet_list[i], meet_list[j]),
                And(Or(before[i][j], before[j][i]), 
                    Not(And(before[i][j], before[j][i])))
            )
            
            # Travel time constraints
            opt.add(Implies(
                And(meet_list[i], meet_list[j], before[i][j]),
                start_list[j] >= end_list[i] + travel_time[loc_list[i]][loc_list[j]]
            ))
            
            opt.add(Implies(
                And(meet_list[i], meet_list[j], before[j][i]),
                start_list[i] >= end_list[j] + travel_time[loc_list[j]][loc_list[i]]
            ))

    # Maximize number of friends met
    opt.maximize(Sum([If(var, 1, 0) for var in meet_vars]))

    # Solve and extract solution
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        
        for i in range(7):
            if is_true(m[meet_vars[i]]):
                start_val = m.eval(start_vars[i]).as_long()
                end_val = m.eval(end_vars[i]).as_long()
                
                # Convert minutes to HH:MM format
                start_time = f"{start_val//60:02d}:{start_val%60:02d}"
                end_time = f"{end_val//60:02d}:{end_val%60:02d}"
                
                itinerary.append({
                    "action": "meet",
                    "person": friends[i]["name"],
                    "start_time": start_time,
                    "end_time": end_time
                })
        
        # Sort meetings chronologically
        itinerary.sort(key=lambda x: x["start_time"])
        print('{"itinerary": ' + str(itinerary).replace("'", '"') + '}')
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()