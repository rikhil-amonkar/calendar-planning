from z3 import *

def min_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    s0 = Int('s0')  # Kevin
    s1 = Int('s1')  # Kimberly
    s2 = 1110       # Joseph
    s3 = 1178       # Thomas

    e0 = s0 + 75
    e1 = s1 + 30
    e2 = s2 + 45
    e3 = s3 + 45

    travel_sunset = [17, 24, 16, 30]
    travel_between = [
        [0, 13, 18, 17],
        [15, 0, 14, 11],
        [18, 14, 0, 23],
        [17, 10, 22, 0]
    ]

    isKevinFirst = Bool('isKevinFirst')

    constraint1 = And(
        s0 == 540 + travel_sunset[0],
        s1 == e0 + travel_between[0][1]
    )

    constraint2 = And(
        s1 == 540 + travel_sunset[1],
        s0 == e1 + travel_between[1][0]
    )

    constraints = [
        Or(And(isKevinFirst, constraint1), And(Not(isKevinFirst), constraint2)),
        s0 >= 495, e0 <= 1290,
        s1 >= 525, e1 <= 750,
        s2 >= 1110, e2 <= 1155,
        s3 >= 1140, e3 <= 1305
    ]

    travel_to_joseph = If(isKevinFirst, 
                          e1 + travel_between[1][2], 
                          e0 + travel_between[0][2])
    constraints.append(s2 >= travel_to_joseph)
    constraints.append(s3 >= e2 + travel_between[2][3])

    total_travel = If(isKevinFirst,
        travel_sunset[0] + travel_between[0][1] + travel_between[1][2] + travel_between[2][3],
        travel_sunset[1] + travel_between[1][0] + travel_between[0][2] + travel_between[2][3]
    )

    opt = Optimize()
    for c in constraints:
        opt.add(c)
    opt.minimize(total_travel)

    if opt.check() == sat:
        m = opt.model()
        s0_val = m.eval(s0).as_long()
        s1_val = m.eval(s1).as_long()
        s2_val = 1110
        s3_val = 1178

        itinerary = [
            {"action": "meet", "person": "Kevin", "start_time": min_to_time(s0_val), "end_time": min_to_time(s0_val + 75)},
            {"action": "meet", "person": "Kimberly", "start_time": min_to_time(s1_val), "end_time": min_to_time(s1_val + 30)},
            {"action": "meet", "person": "Joseph", "start_time": min_to_time(s2_val), "end_time": min_to_time(s2_val + 45)},
            {"action": "meet", "person": "Thomas", "start_time": min_to_time(s3_val), "end_time": min_to_time(s3_val + 45)}
        ]
        print('SOLUTION:')
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print("No solution found")

if __name__ == "__main__":
    main()