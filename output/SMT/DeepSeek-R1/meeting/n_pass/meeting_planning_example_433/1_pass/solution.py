from z3 import *
import json

def main():
    # Travel time matrix: [from_location][to_location]
    travel = [
        [0, 14, 9, 8, 17, 17],   # 0: Nob Hill
        [17, 0, 22, 17, 16, 9],   # 1: Richmond District
        [8, 21, 0, 7, 23, 23],    # 2: Financial District
        [7, 18, 8, 0, 22, 22],    # 3: North Beach
        [16, 16, 20, 20, 0, 11],  # 4: The Castro
        [20, 7, 26, 24, 13, 0]    # 5: Golden Gate Park
    ]
    
    # Friend data: [0: dummy, 1: Emily, 2: Margaret, 3: Ronald, 4: Deborah, 5: Jeffrey]
    names = ["Dummy", "Emily", "Margaret", "Ronald", "Deborah", "Jeffrey"]
    locations = [0, 1, 2, 3, 4, 5]
    available_start = [540, 1140, 990, 1110, 825, 675]  # in minutes
    available_end = [540, 1260, 1215, 1170, 1275, 870]  # in minutes
    durations = [0, 15, 75, 45, 90, 120]
    
    s = Optimize()
    
    # Create variables
    met = [Bool(f"met_{i}") for i in range(1, 6)]  # for friends 1 to 5
    start = [Int(f"start_{i}") for i in range(6)]   # for all 6 meetings (including dummy)
    
    # Fix dummy meeting (0) at Nob Hill, 9:00 AM (540 minutes)
    s.add(start[0] == 540)
    
    # Constraints for meetings 1 to 5
    for i in range(1, 6):
        # If meeting i is scheduled, it must be within the friend's availability
        s.add(Implies(met[i-1], start[i] >= available_start[i]))
        s.add(Implies(met[i-1], start[i] + durations[i] <= available_end[i]))
        # Initial travel constraint from Nob Hill to the friend's location
        s.add(Implies(met[i-1], start[i] >= 540 + travel[0][i]))
    
    # Disjunctive constraints for every pair of meetings (i, j) where i < j and both are scheduled
    for i in range(0, 6):
        for j in range(i+1, 6):
            if i == 0:  # Dummy meeting
                # Only the first part is feasible: start_j >= 540 + travel[0][j]
                # Already enforced by initial travel constraint, so skip
                continue
            else:
                # For two real meetings, ensure travel time between them is accounted for
                s.add(Implies(And(met[i-1], met[j-1]),
                              Or(
                                  start[i] + durations[i] + travel[locations[i]][locations[j]] <= start[j],
                                  start[j] + durations[j] + travel[locations[j]][locations[i]] <= start[i]
                              )))
    
    # Maximize the number of friends met
    s.maximize(Sum([If(m, 1, 0) for m in met]))
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(1, 6):
            if is_true(m[met[i-1]]):
                start_val = m.evaluate(start[i]).as_long()
                end_val = start_val + durations[i]
                # Convert minutes to HH:MM
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
        # Sort meetings by start time
        itinerary.sort(key=lambda x: x["start_time"])
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()