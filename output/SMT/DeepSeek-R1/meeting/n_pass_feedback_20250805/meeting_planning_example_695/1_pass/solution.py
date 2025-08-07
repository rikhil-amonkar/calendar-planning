from z3 import *

def main():
    # Travel times between locations (indices: 0=Bayview, 1=Nob Hill, 2=Union Square, 3=Chinatown, 4=The Castro, 5=Presidio, 6=Pacific Heights, 7=Russian Hill)
    travel_time = [[0] * 8 for _ in range(8)]
    # Bayview to others
    travel_time[0][1] = 20
    travel_time[0][2] = 17
    travel_time[0][3] = 18
    travel_time[0][4] = 20
    travel_time[0][5] = 31
    travel_time[0][6] = 23
    travel_time[0][7] = 23
    # Nob Hill to others
    travel_time[1][0] = 19
    travel_time[1][2] = 7
    travel_time[1][3] = 6
    travel_time[1][4] = 17
    travel_time[1][5] = 17
    travel_time[1][6] = 8
    travel_time[1][7] = 5
    # Union Square to others
    travel_time[2][0] = 15
    travel_time[2][1] = 9
    travel_time[2][3] = 7
    travel_time[2][4] = 19
    travel_time[2][5] = 24
    travel_time[2][6] = 15
    travel_time[2][7] = 13
    # Chinatown to others
    travel_time[3][0] = 22
    travel_time[3][1] = 8
    travel_time[3][2] = 7
    travel_time[3][4] = 22
    travel_time[3][5] = 19
    travel_time[3][6] = 10
    travel_time[3][7] = 7
    # The Castro to others
    travel_time[4][0] = 19
    travel_time[4][1] = 16
    travel_time[4][2] = 19
    travel_time[4][3] = 20
    travel_time[4][5] = 20
    travel_time[4][6] = 16
    travel_time[4][7] = 18
    # Presidio to others
    travel_time[5][0] = 31
    travel_time[5][1] = 18
    travel_time[5][2] = 22
    travel_time[5][3] = 21
    travel_time[5][4] = 21
    travel_time[5][6] = 11
    travel_time[5][7] = 14
    # Pacific Heights to others
    travel_time[6][0] = 22
    travel_time[6][1] = 8
    travel_time[6][2] = 12
    travel_time[6][3] = 11
    travel_time[6][4] = 16
    travel_time[6][5] = 11
    travel_time[6][7] = 7
    # Russian Hill to others
    travel_time[7][0] = 23
    travel_time[7][1] = 5
    travel_time[7][2] = 11
    travel_time[7][3] = 9
    travel_time[7][4] = 21
    travel_time[7][5] = 14
    travel_time[7][6] = 7

    # Friends data: name, location index, start window (minutes from midnight), end window, min duration
    friends = [
        {"name": "Paul", "location": 1, "start_win": 16*60+15, "end_win": 21*60+15, "min_dur": 60},
        {"name": "Carol", "location": 2, "start_win": 18*60, "end_win": 20*60+15, "min_dur": 120},
        {"name": "Patricia", "location": 3, "start_win": 20*60, "end_win": 21*60+30, "min_dur": 75},
        {"name": "Karen", "location": 4, "start_win": 17*60, "end_win": 19*60, "min_dur": 45},
        {"name": "Nancy", "location": 5, "start_win": 11*60+45, "end_win": 22*60, "min_dur": 30},
        {"name": "Jeffrey", "location": 6, "start_win": 20*60, "end_win": 20*60+45, "min_dur": 45},
        {"name": "Matthew", "location": 7, "start_win": 15*60+45, "end_win": 21*60+45, "min_dur": 75}
    ]

    s = Solver()

    # Decision variables for each friend: whether we meet them, and their start time
    meet_vars = [Bool(f"meet_{i}") for i in range(7)]
    start_vars = [Int(f"start_{i}") for i in range(7)]
    end_vars = [Int(f"end_{i}") for i in range(7)]

    # For each friend, set end time and window constraints
    for i in range(7):
        s.add(end_vars[i] == start_vars[i] + friends[i]["min_dur"])
        s.add(If(meet_vars[i], start_vars[i] >= friends[i]["start_win"], True))
        s.add(If(meet_vars[i], end_vars[i] <= friends[i]["end_win"], True))

    # Dummy meeting at Bayview at 9:00 AM (540 minutes from midnight)
    dummy_meet = True
    dummy_start = 540
    dummy_end = 540
    dummy_loc = 0

    # Build lists for all meetings (dummy + friends)
    meet_list = [dummy_meet] + meet_vars
    start_list = [dummy_start] + start_vars
    end_list = [dummy_end] + end_vars
    loc_list = [dummy_loc] + [f["location"] for f in friends]

    # Before matrix: before[i][j] means meeting i is before meeting j
    before = [[Bool(f"before_{i}_{j}") for j in range(8)] for i in range(8)]

    # Constraints for dummy meeting: it must be before any actual meeting that is scheduled
    for j in range(1, 8):
        s.add(before[0][j] == meet_list[j])
        s.add(before[j][0] == False)

    # Constraints for pairs of meetings (excluding dummy to dummy)
    for i in range(8):
        for j in range(8):
            if i == j:
                continue
            if i == 0 and j >= 1:
                continue
            # If both meetings i and j are held, then exactly one of before[i][j] or before[j][i] is true
            s.add(If(And(meet_list[i], meet_list[j]),
                    And(Or(before[i][j], before[j][i]), Not(And(before[i][j], before[j][i]))),
                    True)
            # If both held and i before j, then start_j >= end_i + travel time
            s.add(If(And(meet_list[i], meet_list[j], before[i][j]),
                    start_list[j] >= end_list[i] + travel_time[loc_list[i]][loc_list[j]],
                    True))
            s.add(If(And(meet_list[i], meet_list[j], before[j][i]),
                    start_list[i] >= end_list[j] + travel_time[loc_list[j]][loc_list[i]],
                    True))

    # Objective: maximize the number of friends met
    objective = Sum([If(meet_vars[i], 1, 0) for i in range(7)])
    s.maximize(objective)

    # Solve the problem
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(7):
            if is_true(model[meet_vars[i]]):
                start_val = model.eval(start_vars[i]).as_long()
                end_val = model.eval(end_vars[i]).as_long()
                start_hour = start_val // 60
                start_minute = start_val % 60
                end_hour = end_val // 60
                end_minute = end_val % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friends[i]["name"],
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort meetings by start time
        itinerary.sort(key=lambda x: x["start_time"])
        print({"itinerary": itinerary})
    else:
        print('No solution found')

if __name__ == "__main__":
    main()