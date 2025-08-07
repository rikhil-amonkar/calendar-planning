from z3 import *

def main():
    # Meetings: 0: Thomas, 1: Stephanie, 2: Laura, 3: Betty, 4: Patricia
    names = ["Thomas", "Stephanie", "Laura", "Betty", "Patricia"]
    # Locations: Bayview, Golden Gate Park, Nob Hill, Marina District, Embarcadero
    # Travel time from Fisherman's Wharf to each meeting location
    travel_start = [26, 25, 11, 9, 8]  # in minutes

    # Travel time between meeting locations: 5x5 matrix
    travel = [
        [0, 22, 20, 25, 19],  # from Thomas (0) to others
        [23, 0, 20, 16, 25],   # from Stephanie (1) to others
        [19, 17, 0, 11, 9],    # from Laura (2) to others
        [27, 18, 12, 0, 14],   # from Betty (3) to others
        [21, 25, 10, 12, 0]    # from Patricia (4) to others
    ]

    # Time windows in minutes since midnight
    windows_start = [930, 1110, 525, 1125, 1050]  # start of window
    windows_end = [1110, 1305, 975, 1305, 1320]   # end of window
    min_durations = [120, 30, 30, 45, 45]          # minimum duration per meeting

    # Initialize Z3 solver with optimization
    solver = Optimize()

    # Decision variables
    include = [Bool(f'include_{i}') for i in range(5)]
    start = [Int(f'start_{i}') for i in range(5)]
    end = [Int(f'end_{i}') for i in range(5)]

    # Boolean variables for pairwise order (only for i < j)
    b_pairs = {}
    for i in range(5):
        for j in range(i+1, 5):
            b_pairs[(i, j)] = Bool(f"b_{i}_{j}")

    # Helper function to get the 'before' relation
    def before(i, j):
        if i == j:
            return None
        if i < j:
            return b_pairs[(i, j)]
        else:
            return Not(b_pairs[(j, i)])

    # Constraints for each meeting
    for i in range(5):
        # If meeting is included, enforce time window and duration
        solver.add(Implies(include[i], And(
            start[i] >= windows_start[i],
            end[i] == start[i] + min_durations[i],
            end[i] <= windows_end[i]
        )))
        # Travel time from start location (Fisherman's Wharf at 540 minutes since midnight)
        solver.add(Implies(include[i], start[i] >= 540 + travel_start[i]))

    # Constraints for pairs of meetings (i < j)
    for (i, j) in b_pairs.keys():
        cond = And(include[i], include[j])
        b_ij = b_pairs[(i, j)]
        # If i before j, then end_i + travel[i][j] <= start_j
        c1 = Implies(And(cond, b_ij), end[i] + travel[i][j] <= start[j])
        # If j before i, then end_j + travel[j][i] <= start_i
        c2 = Implies(And(cond, Not(b_ij)), end[j] + travel[j][i] <= start[i])
        solver.add(c1)
        solver.add(c2)

    # Transitivity constraints for every distinct triple (i, j, k)
    for i in range(5):
        for j in range(5):
            if i == j:
                continue
            for k in range(5):
                if k == i or k == j:
                    continue
                cond = And(include[i], include[j], include[k])
                b_ij = before(i, j)
                b_jk = before(j, k)
                b_ik = before(i, k)
                # If (i before j and j before k) then i before k
                solver.add(Implies(cond, Implies(And(b_ij, b_jk), b_ik)))

    # Objective: maximize the number of included meetings
    objective = Sum([If(include[i], 1, 0) for i in range(5)])
    solver.maximize(objective)

    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        included_meetings = []
        for i in range(5):
            if model.evaluate(include[i]):
                start_val = model.evaluate(start[i])
                end_val = model.evaluate(end[i])
                start_val = start_val.as_long()
                end_val = end_val.as_long()
                # Convert to HH:MM format
                start_time = f"{start_val // 60:02d}:{start_val % 60:02d}"
                end_time = f"{end_val // 60:02d}:{end_val % 60:02d}"
                included_meetings.append((start_val, names[i], start_time, end_time))
        
        # Sort meetings by start time
        included_meetings.sort(key=lambda x: x[0])
        itinerary = [{"action": "meet", "person": name, "start_time": st, "end_time": et} 
                    for (_, name, st, et) in included_meetings]
        
        # Output the result in JSON format
        print('SOLUTION:')
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print("No solution found")

if __name__ == "__main__":
    main()