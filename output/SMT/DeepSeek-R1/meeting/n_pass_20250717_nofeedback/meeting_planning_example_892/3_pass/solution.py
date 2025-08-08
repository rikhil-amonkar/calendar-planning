import json
from z3 import *

def main():
    # Define travel times between districts
    travel_data = [
        ('Marina District', 'Bayview', 27),
        ('Marina District', 'Sunset District', 19),
        ('Marina District', 'Richmond District', 11),
        ('Marina District', 'Nob Hill', 12),
        ('Marina District', 'Chinatown', 15),
        ('Marina District', 'Haight-Ashbury', 16),
        ('Marina District', 'North Beach', 11),
        ('Marina District', 'Russian Hill', 8),
        ('Marina District', 'Embarcadero', 14),
        ('Bayview', 'Marina District', 27),
        ('Bayview', 'Sunset District', 23),
        ('Bayview', 'Richmond District', 25),
        ('Bayview', 'Nob Hill', 20),
        ('Bayview', 'Chinatown', 19),
        ('Bayview', 'Haight-Ashbury', 19),
        ('Bayview', 'North Beach', 22),
        ('Bayview', 'Russian Hill', 23),
        ('Bayview', 'Embarcadero', 19),
        ('Sunset District', 'Marina District', 21),
        ('Sunset District', 'Bayview', 22),
        ('Sunset District', 'Richmond District', 12),
        ('Sunset District', 'Nob Hill', 27),
        ('Sunset District', 'Chinatown', 30),
        ('Sunset District', 'Haight-Ashbury', 15),
        ('Sunset District', 'North Beach', 28),
        ('Sunset District', 'Russian Hill', 24),
        ('Sunset District', 'Embarcadero', 30),
        ('Richmond District', 'Marina District', 9),
        ('Richmond District', 'Bayview', 27),
        ('Richmond District', 'Sunset District', 11),
        ('Richmond District', 'Nob Hill', 17),
        ('Richmond District', 'Chinatown', 20),
        ('Richmond District', 'Haight-Ashbury', 10),
        ('Richmond District', 'North Beach', 17),
        ('Richmond District', 'Russian Hill', 13),
        ('Richmond District', 'Embarcadero', 19),
        ('Nob Hill', 'Marina District', 11),
        ('Nob Hill', 'Bayview', 19),
        ('Nob Hill', 'Sunset District', 24),
        ('Nob Hill', 'Richmond District', 14),
        ('Nob Hill', 'Chinatown', 6),
        ('Nob Hill', 'Haight-Ashbury', 13),
        ('Nob Hill', 'North Beach', 8),
        ('Nob Hill', 'Russian Hill', 5),
        ('Nob Hill', 'Embarcadero', 9),
        ('Chinatown', 'Marina District', 12),
        ('Chinatown', 'Bayview', 20),
        ('Chinatown', 'Sunset District', 29),
        ('Chinatown', 'Richmond District', 20),
        ('Chinatown', 'Nob Hill', 9),
        ('Chinatown', 'Haight-Ashbury', 19),
        ('Chinatown', 'North Beach', 3),
        ('Chinatown', 'Russian Hill', 7),
        ('Chinatown', 'Embarcadero', 5),
        ('Haight-Ashbury', 'Marina District', 17),
        ('Haight-Ashbury', 'Bayview', 18),
        ('Haight-Ashbury', 'Sunset District', 15),
        ('Haight-Ashbury', 'Richmond District', 10),
        ('Haight-Ashbury', 'Nob Hill', 15),
        ('Haight-Ashbury', 'Chinatown', 19),
        ('Haight-Ashbury', 'North Beach', 19),
        ('Haight-Ashbury', 'Russian Hill', 17),
        ('Haight-Ashbury', 'Embarcadero', 20),
        ('North Beach', 'Marina District', 9),
        ('North Beach', 'Bayview', 25),
        ('North Beach', 'Sunset District', 27),
        ('North Beach', 'Richmond District', 18),
        ('North Beach', 'Nob Hill', 7),
        ('North Beach', 'Chinatown', 6),
        ('North Beach', 'Haight-Ashbury', 18),
        ('North Beach', 'Russian Hill', 4),
        ('North Beach', 'Embarcadero', 6),
        ('Russian Hill', 'Marina District', 7),
        ('Russian Hill', 'Bayview', 23),
        ('Russian Hill', 'Sunset District', 23),
        ('Russian Hill', 'Richmond District', 14),
        ('Russian Hill', 'Nob Hill', 5),
        ('Russian Hill', 'Chinatown', 9),
        ('Russian Hill', 'Haight-Ashbury', 17),
        ('Russian Hill', 'North Beach', 5),
        ('Russian Hill', 'Embarcadero', 8),
        ('Embarcadero', 'Marina District', 12),
        ('Embarcadero', 'Bayview', 21),
        ('Embarcadero', 'Sunset District', 30),
        ('Embarcadero', 'Richmond District', 21),
        ('Embarcadero', 'Nob Hill', 10),
        ('Embarcadero', 'Chinatown', 7),
        ('Embarcadero', 'Haight-Ashbury', 21),
        ('Embarcadero', 'North Beach', 5),
        ('Embarcadero', 'Russian Hill', 8)
    ]
    
    travel_dict = {}
    for (f, t, d) in travel_data:
        travel_dict[(f, t)] = d

    friends = [
        ("Charles", "Bayview", 150, 330, 45),  # 11:30AM to 2:30PM
        ("Robert", "Sunset District", 465, 720, 30),  # 4:45PM to 9:00PM
        ("Karen", "Richmond District", 615, 750, 60),  # 7:15PM to 9:30PM
        ("Rebecca", "Nob Hill", 435, 690, 90),  # 4:15PM to 8:30PM
        ("Margaret", "Chinatown", 315, 645, 120),  # 2:15PM to 7:45PM
        ("Patricia", "Haight-Ashbury", 330, 690, 45),  # 2:30PM to 8:30PM
        ("Mark", "North Beach", 300, 570, 105),  # 2:00PM to 6:30PM
        ("Melissa", "Russian Hill", 240, 645, 30),  # 1:00PM to 7:45PM
        ("Laura", "Embarcadero", -75, 255, 105)  # 7:45AM to 1:15PM
    ]

    n_friends = len(friends)
    n_positions = n_friends

    opt = Optimize()
    assign = [[Bool(f"assign_{p}_{i}") for i in range(n_friends)] for p in range(n_positions)]
    used = [Bool(f"used_{p}") for p in range(n_positions)]
    start_time = [Int(f"start_{p}") for p in range(n_positions)]
    end_time = [Int(f"end_{p}") for p in range(n_positions)]

    # Constraint: Each position has at most one friend
    for p in range(n_positions):
        opt.add(AtMost(*assign[p], 1))
        opt.add(used[p] == Or(assign[p]))

    # Constraint: Each friend is assigned to at most one position
    for i in range(n_friends):
        opt.add(AtMost(*[assign[p][i] for p in range(n_positions)], 1))

    # Constraint: Meeting times within availability and duration
    for p in range(n_positions):
        for i in range(n_friends):
            opt.add(Implies(assign[p][i],
                          And(start_time[p] >= friends[i][2],
                              end_time[p] == start_time[p] + friends[i][4],
                              end_time[p] <= friends[i][3])))

    # Travel from Marina to first meeting
    for i in range(n_friends):
        t0 = travel_dict[("Marina District", friends[i][1])]
        opt.add(Implies(assign[0][i], start_time[0] >= t0))

    # Travel between consecutive meetings (with same-district check)
    for p in range(1, n_positions):
        for i in range(n_friends):
            for j in range(n_friends):
                dist_i = friends[i][1]
                dist_j = friends[j][1]
                if dist_i == dist_j:
                    travel_time = 0
                else:
                    travel_time = travel_dict[(dist_i, dist_j)]
                opt.add(Implies(And(assign[p-1][i], assign[p][j]),
                              start_time[p] >= end_time[p-1] + travel_time))

    # Chain of used positions
    for p in range(1, n_positions):
        opt.add(Implies(Not(used[p-1]), Not(used[p])))

    # Maximize the number of used positions
    total_used = Sum([If(used[p], 1, 0) for p in range(n_positions)])
    opt.maximize(total_used)

    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for p in range(n_positions):
            if is_true(m.eval(used[p])):
                for i in range(n_friends):
                    if is_true(m.eval(assign[p][i])):
                        name = friends[i][0]
                        start_val = m.eval(start_time[p]).as_long()
                        end_val = m.eval(end_time[p]).as_long()
                        # Convert to time from 9:00AM: start_val in minutes
                        total_minutes_start = start_val
                        start_hour = 9 + total_minutes_start // 60
                        start_minute = total_minutes_start % 60
                        total_minutes_end = end_val
                        end_hour = 9 + total_minutes_end // 60
                        end_minute = total_minutes_end % 60
                        start_str = f"{start_hour:02d}:{start_minute:02d}"
                        end_str = f"{end_hour:02d}:{end_minute:02d}"
                        itinerary.append({"action": "meet", "person": name, "start_time": start_str, "end_time": end_str})
        print('SOLUTION:')
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()