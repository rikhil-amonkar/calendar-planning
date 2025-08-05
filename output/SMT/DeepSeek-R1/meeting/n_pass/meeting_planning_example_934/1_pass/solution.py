from z3 import *
import json

def main():
    friends = [
        ("Mary", "Embarcadero", 660, 735, 75),
        ("Kenneth", "The Castro", 135, 615, 30),
        ("Joseph", "Haight-Ashbury", 660, 780, 120),
        ("Sarah", "Union Square", 165, 330, 90),
        ("Thomas", "North Beach", 615, 645, 15),
        ("Daniel", "Pacific Heights", 285, 690, 15),
        ("Richard", "Chinatown", 0, 585, 30),
        ("Mark", "Golden Gate Park", 510, 750, 120),
        ("David", "Marina District", 660, 720, 60),
        ("Karen", "Russian Hill", 255, 570, 120)
    ]
    virtual = ("Start", "Nob Hill", 0, 0, 0)
    all_meetings = [virtual] + friends

    travel_dict = {
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Russian Hill"): 5,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Russian Hill"): 8,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Chinatown"): 22,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Russian Hill"): 18,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "The Castro"): 17,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Russian Hill"): 13,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "The Castro"): 23,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Russian Hill"): 4,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Russian Hill"): 7,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Russian Hill"): 8,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Marina District"): 7
    }

    n = len(all_meetings)
    meet = [None] * n
    T = [None] * n

    meet[0] = True
    T[0] = 0

    for i in range(1, n):
        meet[i] = Bool(f'meet_{i}')
        T[i] = Int(f'T_{i}')

    s = Solver()

    for i in range(1, n):
        _, _, avail_start, avail_end, dur = all_meetings[i]
        s.add(Implies(meet[i], And(T[i] >= avail_start, T[i] + dur <= avail_end)))

    for i in range(n):
        for j in range(i+1, n):
            loc_i = all_meetings[i][1]
            loc_j = all_meetings[j][1]
            dur_i = all_meetings[i][4]
            dur_j = all_meetings[j][4]
            travel_ij = travel_dict.get((loc_i, loc_j))
            travel_ji = travel_dict.get((loc_j, loc_i))
            if travel_ij is None or travel_ji is None:
                continue

            if i == 0:
                cond = meet[j]
            else:
                cond = And(meet[i], meet[j])
            option1 = (T[i] + dur_i + travel_ij <= T[j])
            option2 = (T[j] + dur_j + travel_ji <= T[i])
            s.add(Implies(cond, Or(option1, option2)))

    opt = Optimize()
    opt.add(s.assertions())
    objective = Sum([If(meet[i], 1, 0) for i in range(1, n)])
    opt.maximize(objective)

    if opt.check() == sat:
        m = opt.model()
        schedule = []
        for i in range(1, n):
            if m.evaluate(meet[i]):
                person = all_meetings[i][0]
                start_val = m.evaluate(T[i])
                if isinstance(start_val, IntNumRef):
                    start_min = start_val.as_long()
                else:
                    start_min = int(str(start_val))
                dur = all_meetings[i][4]
                end_min = start_min + dur
                start_hour = 9 + start_min // 60
                start_minute = start_min % 60
                end_hour = 9 + end_min // 60
                end_minute = end_min % 60
                start_time = f"{start_hour:02d}:{start_minute:02d}"
                end_time = f"{end_hour:02d}:{end_minute:02d}"
                schedule.append({
                    "action": "meet",
                    "person": person,
                    "start_time": start_time,
                    "end_time": end_time
                })
        schedule.sort(key=lambda x: x['start_time'])
        result = {"itinerary": schedule}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()