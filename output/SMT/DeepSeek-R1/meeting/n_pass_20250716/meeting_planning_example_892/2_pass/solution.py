from z3 import *

def main():
    # Travel matrix: 10x10, index 0 is Marina (dummy), indices 1-9 are the friends' districts
    travel_matrix = [
        [0, 27, 19, 11, 12, 15, 16, 11, 8, 14],
        [27, 0, 23, 25, 20, 19, 19, 22, 23, 19],
        [21, 22, 0, 12, 27, 30, 15, 28, 24, 30],
        [9, 27, 11, 0, 17, 20, 10, 17, 13, 19],
        [11, 19, 24, 14, 0, 6, 13, 8, 5, 9],
        [12, 20, 29, 20, 9, 0, 19, 3, 7, 5],
        [17, 18, 15, 10, 15, 19, 0, 19, 17, 20],
        [9, 25, 27, 18, 7, 6, 18, 0, 4, 6],
        [7, 23, 23, 14, 5, 9, 17, 5, 0, 8],
        [12, 21, 30, 21, 10, 7, 21, 5, 8, 0]
    ]
    
    # Minimum meeting durations: index 0 (dummy) is 0, indices 1-9 for friends
    min_dur = [0, 45, 30, 60, 90, 120, 45, 105, 30, 105]
    
    # Available start times (minutes from 9:00 AM)
    available_start = [0, 150, 465, 615, 435, 315, 330, 300, 240, -75]
    
    # Available end times (minutes from 9:00 AM)
    available_end = [0, 330, 720, 750, 690, 645, 690, 570, 645, 255]
    
    solver = Optimize()
    
    n = 10  # 1 dummy + 9 friends
    meet = [None] * n
    start = [None] * n
    end = [None] * n
    
    # Dummy meeting (Marina District) at time 0
    meet[0] = True
    start[0] = 0
    end[0] = 0
    
    # Initialize variables for friends (indices 1-9)
    for i in range(1, n):
        meet[i] = Bool(f"meet_{i}")
        start[i] = Int(f"start_{i}")
        end[i] = Int(f"end_{i}")
    
    # Constraints for each friend if met
    for i in range(1, n):
        constraints = [
            end[i] == start[i] + min_dur[i],
            start[i] >= available_start[i],
            end[i] <= available_end[i],
            start[i] >= 0,
            end[i] >= 0
        ]
        solver.add(Implies(meet[i], And(constraints)))
    
    # Disjunctive constraints for all pairs (i, j) including dummy
    for i in range(n):
        for j in range(i+1, n):
            if i == 0:  # Dummy is fixed and always present
                constraint = start[j] >= end[i] + travel_matrix[i][j]
                solver.add(Implies(meet[j], constraint))
            else:
                # For two non-dummy meetings, or one non-dummy and j (but i>=1, j>i)
                disjunction = Or(
                    start[i] >= end[j] + travel_matrix[j][i],
                    start[j] >= end[i] + travel_matrix[i][j]
                )
                solver.add(Implies(And(meet[i], meet[j]), disjunction))
    
    # Objective: maximize the number of friends met
    objective = Sum([If(meet[i], 1, 0) for i in range(1, n)])
    solver.maximize(objective)
    
    if solver.check() == sat:
        model = solver.model()
        num_met = model.evaluate(objective)
        print(f"Number of friends met: {num_met}")
        
        # Collect and sort meetings by start time
        meetings = []
        friend_names = {
            1: "Charles (Bayview)",
            2: "Robert (Sunset District)",
            3: "Karen (Richmond District)",
            4: "Rebecca (Nob Hill)",
            5: "Margaret (Chinatown)",
            6: "Patricia (Haight-Ashbury)",
            7: "Mark (North Beach)",
            8: "Melissa (Russian Hill)",
            9: "Laura (Embarcadero)"
        }
        for i in range(1, n):
            if model[meet[i]]:
                s_val = model[start[i]].as_long()
                e_val = model[end[i]].as_long()
                meetings.append((i, s_val, e_val))
        
        meetings.sort(key=lambda x: x[1])
        
        print("Schedule (times from 9:00 AM in minutes):")
        for idx, s, e in meetings:
            name = friend_names[idx]
            print(f"  - {name}: start at {s}, end at {e} (duration: {e-s} minutes)")
        
        print("\nSchedule in 24-hour format:")
        for idx, s, e in meetings:
            name = friend_names[idx]
            start_hour = 9 + s // 60
            start_min = s % 60
            end_hour = 9 + e // 60
            end_min = e % 60
            print(f"  - {name}: {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()