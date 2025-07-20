from z3 import *

def main():
    travel_data = [
        ("Union Square", "The Castro", 17),
        ("Union Square", "North Beach", 10),
        ("Union Square", "Embarcadero", 11),
        ("Union Square", "Alamo Square", 15),
        ("Union Square", "Nob Hill", 9),
        ("Union Square", "Presidio", 24),
        ("Union Square", "Fisherman's Wharf", 15),
        ("Union Square", "Mission District", 14),
        ("Union Square", "Haight-Ashbury", 18),
        ("The Castro", "Union Square", 19),
        ("The Castro", "North Beach", 20),
        ("The Castro", "Embarcadero", 22),
        ("The Castro", "Alamo Square", 8),
        ("The Castro", "Nob Hill", 16),
        ("The Castro", "Presidio", 20),
        ("The Castro", "Fisherman's Wharf", 24),
        ("The Castro", "Mission District", 7),
        ("The Castro", "Haight-Ashbury", 6),
        ("North Beach", "Union Square", 7),
        ("North Beach", "The Castro", 23),
        ("North Beach", "Embarcadero", 6),
        ("North Beach", "Alamo Square", 16),
        ("North Beach", "Nob Hill", 7),
        ("North Beach", "Presidio", 17),
        ("North Beach", "Fisherman's Wharf", 5),
        ("North Beach", "Mission District", 18),
        ("North Beach", "Haight-Ashbury", 18),
        ("Embarcadero", "Union Square", 10),
        ("Embarcadero", "The Castro", 25),
        ("Embarcadero", "North Beach", 5),
        ("Embarcadero", "Alamo Square", 19),
        ("Embarcadero", "Nob Hill", 10),
        ("Embarcadero", "Presidio", 20),
        ("Embarcadero", "Fisherman's Wharf", 6),
        ("Embarcadero", "Mission District", 20),
        ("Embarcadero", "Haight-Ashbury", 21),
        ("Alamo Square", "Union Square", 14),
        ("Alamo Square", "The Castro", 8),
        ("Alamo Square", "North Beach", 15),
        ("Alamo Square", "Embarcadero", 16),
        ("Alamo Square", "Nob Hill", 11),
        ("Alamo Square", "Presidio", 17),
        ("Alamo Square", "Fisherman's Wharf", 19),
        ("Alamo Square", "Mission District", 10),
        ("Alamo Square", "Haight-Ashbury", 5),
        ("Nob Hill", "Union Square", 7),
        ("Nob Hill", "The Castro", 17),
        ("Nob Hill", "North Beach", 8),
        ("Nob Hill", "Embarcadero", 9),
        ("Nob Hill", "Alamo Square", 11),
        ("Nob Hill", "Presidio", 17),
        ("Nob Hill", "Fisherman's Wharf", 10),
        ("Nob Hill", "Mission District", 13),
        ("Nob Hill", "Haight-Ashbury", 13),
        ("Presidio", "Union Square", 22),
        ("Presidio", "The Castro", 21),
        ("Presidio", "North Beach", 18),
        ("Presidio", "Embarcadero", 20),
        ("Presidio", "Alamo Square", 19),
        ("Presidio", "Nob Hill", 18),
        ("Presidio", "Fisherman's Wharf", 19),
        ("Presidio", "Mission District", 26),
        ("Presidio", "Haight-Ashbury", 15),
        ("Fisherman's Wharf", "Union Square", 13),
        ("Fisherman's Wharf", "The Castro", 27),
        ("Fisherman's Wharf", "North Beach", 6),
        ("Fisherman's Wharf", "Embarcadero", 8),
        ("Fisherman's Wharf", "Alamo Square", 21),
        ("Fisherman's Wharf", "Nob Hill", 11),
        ("Fisherman's Wharf", "Presidio", 17),
        ("Fisherman's Wharf", "Mission District", 22),
        ("Fisherman's Wharf", "Haight-Ashbury", 22),
        ("Mission District", "Union Square", 15),
        ("Mission District", "The Castro", 7),
        ("Mission District", "North Beach", 17),
        ("Mission District", "Embarcadero", 19),
        ("Mission District", "Alamo Square", 11),
        ("Mission District", "Nob Hill", 12),
        ("Mission District", "Presidio", 25),
        ("Mission District", "Fisherman's Wharf", 22),
        ("Mission District", "Haight-Ashbury", 12),
        ("Haight-Ashbury", "Union Square", 19),
        ("Haight-Ashbury", "The Castro", 6),
        ("Haight-Ashbury", "North Beach", 19),
        ("Haight-Ashbury", "Embarcadero", 20),
        ("Haight-Ashbury", "Alamo Square", 5),
        ("Haight-Ashbury", "Nob Hill", 15),
        ("Haight-Ashbury", "Presidio", 15),
        ("Haight-Ashbury", "Fisherman's Wharf", 23),
        ("Haight-Ashbury", "Mission District", 11)
    ]

    travel_dict = {}
    for (from_loc, to_loc, time) in travel_data:
        travel_dict[(from_loc, to_loc)] = time

    friends = [
        ("Melissa", "The Castro", 675, 735, 30),
        ("Kimberly", "North Beach", 0, 90, 15),
        ("Joseph", "Embarcadero", 390, 630, 75),
        ("Barbara", "Alamo Square", 705, 765, 15),
        ("Kenneth", "Nob Hill", 195, 495, 105),
        ("Joshua", "Presidio", 450, 555, 105),
        ("Brian", "Fisherman's Wharf", 30, 390, 45),
        ("Steven", "Mission District", 630, 720, 90),
        ("Betty", "Haight-Ashbury", 600, 690, 90)
    ]

    s = Optimize()
    n = len(friends)

    meet = [Bool(f'meet_{i}') for i in range(n)]
    order = [Int(f'order_{i}') for i in range(n)]
    start = [Int(f'start_{i}') for i in range(n)]

    for i in range(n):
        s.add(Implies(meet[i], order[i] >= 1))
        s.add(Implies(meet[i], order[i] <= n))
        s.add(Implies(meet[i], start[i] >= friends[i][2]))
        s.add(Implies(meet[i], start[i] + friends[i][4] <= friends[i][3]))

    for i in range(n):
        for j in range(i+1, n):
            s.add(Implies(And(meet[i], meet[j]), order[i] != order[j]))

    for i in range(n):
        cond = And(meet[i], order[i] == 1)
        s.add(Implies(cond, start[i] >= travel_dict[("Union Square", friends[i][1])]))

    for i in range(n):
        cond = And(meet[i], order[i] >= 2)
        disj = []
        for j in range(n):
            if i == j:
                continue
            loc_i = friends[i][1]
            loc_j = friends[j][1]
            travel_time = travel_dict[(loc_j, loc_i)]
            conj = And(
                meet[j],
                order[j] == order[i] - 1,
                start[i] >= start[j] + friends[j][4] + travel_time
            )
            disj.append(conj)
        s.add(Implies(cond, Or(disj)))

    count_meet = Sum([If(meet[i], 1, 0) for i in range(n)])
    s.maximize(count_meet)

    if s.check() == sat:
        m = s.model()
        total_met = 0
        schedule = []
        for i in range(n):
            if m.eval(meet[i]):
                total_met += 1
                name = friends[i][0]
                loc = friends[i][1]
                st = m.eval(start[i]).as_long()
                dur = friends[i][4]
                ord_val = m.eval(order[i]).as_long()
                schedule.append((ord_val, name, loc, st, st + dur))
        schedule.sort(key=lambda x: x[0])
        print(f"Total friends met: {total_met}")
        for ord_val, name, loc, st, et in schedule:
            st_hour = 9 + st // 60
            st_minute = st % 60
            et_hour = 9 + et // 60
            et_minute = et % 60
            print(f"Order {ord_val}: {name} at {loc} from {st_hour:02d}:{st_minute:02d} to {et_hour:02d}:{et_minute:02d}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()