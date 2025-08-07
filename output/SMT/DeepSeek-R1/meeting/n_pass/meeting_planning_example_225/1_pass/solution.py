from z3 import *
import json

def main():
    # Initialize variables
    L = Int('L')
    A0 = Int('A0')  # Sarah (North Beach)
    A1 = Int('A1')  # Jeffrey (Union Square)
    A2 = Int('A2')  # Brian (Alamo Square)
    attend0 = Bool('attend0')
    attend1 = Bool('attend1')
    attend2 = Bool('attend2')
    A = [A0, A1, A2]
    attend = [attend0, attend1, attend2]
    names = ["Sarah", "Jeffrey", "Brian"]
    durations = [60, 75, 75]  # Minimum meeting durations in minutes
    
    # Travel times from Sunset to each location
    T_start = [29, 30, 17]  # To Sarah, Jeffrey, Brian
    
    # Travel time matrix between locations: [Sarah, Jeffrey, Brian]
    T = [
        [0, 7, 16],  # From Sarah (North Beach) to others
        [10, 0, 15], # From Jeffrey (Union Square) to others
        [15, 14, 0]  # From Brian (Alamo Square) to others
    ]
    
    # Initialize solver with optimization
    solver = Optimize()
    
    # Constraint: Leave Sunset no earlier than 9:00 AM (540 minutes)
    solver.add(L >= 540)
    
    # Constraints for each friend
    for i in range(3):
        # If attending, arrival time must account for travel from Sunset
        solver.add(Implies(attend[i], A[i] >= L + T_start[i]))
        # Time window constraints
        if i == 0:  # Sarah: 4:00 PM to 6:15 PM (960 to 1095 minutes)
            solver.add(Implies(attend[i], And(A[i] >= 960, A[i] + durations[i] <= 1095)))
        elif i == 1:  # Jeffrey: 3:00 PM to 10:00 PM (900 to 1320 minutes)
            solver.add(Implies(attend[i], And(A[i] >= 900, A[i] + durations[i] <= 1320)))
        else:  # Brian: 4:00 PM to 5:30 PM (960 to 1050 minutes)
            solver.add(Implies(attend[i], And(A[i] >= 960, A[i] + durations[i] <= 1050)))
    
    # Constraints for pairwise meetings
    for i in range(3):
        for j in range(3):
            if i != j:
                # If both meetings are attended, ensure travel time between them
                solver.add(Implies(And(attend[i], attend[j]),
                            Or(A[j] >= A[i] + durations[i] + T[i][j],
                               A[i] >= A[j] + durations[j] + T[j][i])))
    
    # Maximize the number of friends met
    count = Sum([If(attend[i], 1, 0) for i in range(3)])
    solver.maximize(count)
    
    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(3):
            if is_true(model[attend[i]]):
                start_val = model[A[i]].as_long()
                end_val = start_val + durations[i]
                start_hour = start_val // 60
                start_minute = start_val % 60
                end_hour = end_val // 60
                end_minute = end_val % 60
                start_time = f"{start_hour:02d}:{start_minute:02d}"
                end_time = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": names[i],
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()