from z3 import *
import json

def main():
    # Data definitions
    names = ["Emily", "Helen", "Kimberly", "James", "Linda", "Paul", "Anthony", "Nancy", "William", "Margaret"]
    starts_avail = [555, 825, 1125, 630, 450, 885, 480, 510, 1050, 915]  # in minutes from midnight
    ends_avail = [825, 1125, 1275, 690, 1155, 1125, 885, 825, 1230, 1095]
    min_durations = [120, 30, 75, 30, 15, 90, 105, 120, 120, 45]
    travel_start = [7, 5, 21, 8, 17, 7, 16, 15, 23, 14]  # travel times from Russian Hill

    # Travel matrix between friends (10x10), [i][j] = travel time from friend i to friend j
    travel_matrix = [
        [0, 9, 15, 10, 11, 13, 15, 10, 22, 12],
        [8, 0, 22, 6, 18, 5, 18, 16, 25, 18],
        [16, 23, 0, 25, 7, 24, 17, 9, 23, 7],
        [11, 5, 25, 0, 21, 6, 20, 19, 21, 21],
        [12, 19, 7, 20, 0, 23, 11, 5, 18, 10],
        [12, 6, 25, 8, 22, 0, 22, 21, 26, 18],
        [16, 17, 17, 19, 12, 22, 0, 11, 14, 20],
        [10, 15, 9, 16, 5, 19, 10, 0, 16, 11],
        [23, 22, 22, 19, 19, 25, 13, 16, 0, 25],
        [10, 17, 9, 19, 10, 18, 20, 13, 27, 0]
    ]

    n = len(names)

    # Initialize solver and variables
    opt = Optimize()
    met = [Bool(f'met_{i}') for i in range(n)]
    next_vars = [Int(f'next_{i}') for i in range(n)]  # next_vars[i] in [0,9] for next meeting, or 10 for none
    in_degree = [Int(f'in_degree_{i}') for i in range(n)]
    arrival = [Real(f'arrival_{i}') for i in range(n)]
    start_t = [Real(f'start_{i}') for i in range(n)]
    end_t = [Real(f'end_{i}') for i in range(n)]

    # Constraints for next_vars: if met[i] is True, next_vars[i] is in [0,9] and not i, or 10 (none). Else, 10.
    for i in range(n):
        opt.add(If(met[i], Or(And(next_vars[i] >= 0, next_vars[i] < n, next_vars[i] != i), next_vars[i] == 10), next_vars[i] == 10))

    # in_degree[i] = number of j such that next_vars[j] == i
    for i in range(n):
        opt.add(in_degree[i] == Sum([If(And(met[j], next_vars[j] == i), 1, 0) for j in range(n)]))

    # Constraints for in_degree: exactly one start meeting (in_degree[i]==0 and met[i]), and for non-start met meetings, in_degree[i]==1
    start_meeting_count = Sum([If(And(met[i], in_degree[i] == 0), 1, 0) for i in range(n)])
    opt.add(start_meeting_count == 1)
    for i in range(n):
        opt.add(If(met[i], 
                    If(in_degree[i] == 0, True, in_degree[i] == 1),
                    in_degree[i] == 0))

    # If next_vars[i] points to j, then j must be met
    for i in range(n):
        opt.add(If(And(met[i], next_vars[i] != 10),
                    And(met[next_vars[i]], next_vars[i] != i),
                    True))

    # Arrival, start, and end time constraints
    for i in range(n):
        # If meeting i is the start meeting (in_degree[i] == 0), then arrival[i] = 540 (9:00 AM) + travel_start[i]
        opt.add(If(And(met[i], in_degree[i] == 0),
                    arrival[i] == 540 + travel_start[i],
                    True))
        # For all j, if j is the predecessor of i (next_vars[j] == i), then arrival[i] = end_t[j] + travel_matrix[j][i]
        for j in range(n):
            opt.add(If(And(met[i], met[j], next_vars[j] == i),
                        arrival[i] == end_t[j] + travel_matrix[j][i],
                        True))
        # Meeting time constraints: start_t[i] >= max(arrival[i], starts_avail[i]), end_t[i] = start_t[i] + min_durations[i], and end_t[i] <= ends_avail[i]
        opt.add(If(met[i],
                    And(
                        start_t[i] >= arrival[i],
                        start_t[i] >= starts_avail[i],
                        end_t[i] == start_t[i] + min_durations[i],
                        end_t[i] <= ends_avail[i]
                    ),
                    True))

    # Maximize the number of meetings
    num_met = Sum([If(met[i], 1, 0) for i in range(n)])
    opt.maximize(num_met)

    # Solve
    if opt.check() == sat:
        model = opt.model()
        # Extract results
        meetings = []
        for i in range(n):
            if is_true(model.eval(met[i])):
                start_minutes = int(round(float(model.eval(start_t[i]).as_fraction())))
                end_minutes = int(round(float(model.eval(end_t[i]).as_fraction())))
                start_h = start_minutes // 60
                start_m = start_minutes % 60
                end_h = end_minutes // 60
                end_m = end_minutes % 60
                start_str = f"{start_h:02d}:{start_m:02d}"
                end_str = f"{end_h:02d}:{end_m:02d}"
                meetings.append({
                    "action": "meet",
                    "person": names[i],
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort meetings by start_time
        meetings.sort(key=lambda x: x['start_time'])
        result = {"itinerary": meetings}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()