from z3 import *

def min_to_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    M_start = Int('M_start')
    M_end = M_start + 15  # 15 minutes meeting

    N_start = Int('N_start')
    N_end = N_start + 105  # 105 minutes meeting

    E_start = Int('E_start')
    E_end = E_start + 120  # 120 minutes meeting

    order_M = Int('order_M')
    order_N = Int('order_N')
    order_E = Int('order_E')

    s = Solver()

    # Availability constraints
    s.add(M_start >= 510)   # 8:30 AM
    s.add(M_end <= 1200)    # 8:00 PM
    s.add(N_start >= 1185)  # 7:45 PM
    s.add(N_end <= 1320)    # 10:00 PM
    s.add(E_start >= 1005)  # 4:45 PM
    s.add(E_end <= 1320)    # 10:00 PM

    # Order constraints: each meeting has a unique order 0,1,2
    s.add(order_M >= 0, order_M <= 2)
    s.add(order_N >= 0, order_N <= 2)
    s.add(order_E >= 0, order_E <= 2)
    s.add(Distinct(order_M, order_N, order_E))

    # Travel constraints for all 6 permutations
    s.add(Or(
        And(order_M == 0, order_N == 1, order_E == 2,
            M_start >= 540 + 25, 
            N_start >= M_end + 11,
            E_start >= N_end + 7),
        And(order_M == 0, order_E == 1, order_N == 2,
            M_start >= 540 + 25,
            E_start >= M_end + 7,
            N_start >= E_end + 7),
        And(order_N == 0, order_M == 1, order_E == 2,
            N_start >= 540 + 17,
            M_start >= N_end + 12,
            E_start >= M_end + 7),
        And(order_N == 0, order_E == 1, order_M == 2,
            N_start >= 540 + 17,
            E_start >= N_end + 7,
            M_start >= E_end + 9),
        And(order_E == 0, order_M == 1, order_N == 2,
            E_start >= 540 + 18,
            M_start >= E_end + 9,
            N_start >= M_end + 11),
        And(order_E == 0, order_N == 1, order_M == 2,
            E_start >= 540 + 18,
            N_start >= E_end + 7,
            M_start >= N_end + 12)
    ))

    result = None
    if s.check() == sat:
        m = s.model()
        meetings = [
            {"action": "meet", "person": "Melissa", 
             "start_time": min_to_time(m.eval(M_start).as_long()), 
             "end_time": min_to_time(m.eval(M_end).as_long())},
            {"action": "meet", "person": "Nancy", 
             "start_time": min_to_time(m.eval(N_start).as_long()), 
             "end_time": min_to_time(m.eval(N_end).as_long())},
            {"action": "meet", "person": "Emily", 
             "start_time": min_to_time(m.eval(E_start).as_long()), 
             "end_time": min_to_time(m.eval(E_end).as_long())}
        ]
        meetings_sorted = sorted(meetings, key=lambda x: x['start_time'])
        result = {'itinerary': meetings_sorted}
    else:
        s2 = Solver()
        s2.add(N_start >= 1185, N_end <= 1320)
        s2.add(E_start >= 1005, E_end <= 1320)
        order_N2 = Int('order_N2')
        order_E2 = Int('order_E2')
        s2.add(order_N2 >= 0, order_N2 <= 1)
        s2.add(order_E2 >= 0, order_E2 <= 1)
        s2.add(Distinct(order_N2, order_E2))
        s2.add(Or(
            And(order_N2 == 0, order_E2 == 1,
                N_start >= 540 + 17,
                E_start >= N_end + 7),
            And(order_E2 == 0, order_N2 == 1,
                E_start >= 540 + 18,
                N_start >= E_end + 7)
        ))
        if s2.check() == sat:
            m2 = s2.model()
            meetings = [
                {"action": "meet", "person": "Nancy", 
                 "start_time": min_to_time(m2.eval(N_start).as_long()), 
                 "end_time": min_to_time(m2.eval(N_end).as_long())},
                {"action": "meet", "person": "Emily", 
                 "start_time": min_to_time(m2.eval(E_start).as_long()), 
                 "end_time": min_to_time(m2.eval(E_end).as_long())}
            ]
            meetings_sorted = sorted(meetings, key=lambda x: x['start_time'])
            result = {'itinerary': meetings_sorted}
        else:
            s3 = Solver()
            s3.add(M_start >= 510, M_end <= 1200)
            s3.add(E_start >= 1005, E_end <= 1320)
            order_M3 = Int('order_M3')
            order_E3 = Int('order_E3')
            s3.add(order_M3 >= 0, order_M3 <= 1)
            s3.add(order_E3 >= 0, order_E3 <= 1)
            s3.add(Distinct(order_M3, order_E3))
            s3.add(Or(
                And(order_M3 == 0, order_E3 == 1,
                    M_start >= 540 + 25,
                    E_start >= M_end + 7),
                And(order_E3 == 0, order_M3 == 1,
                    E_start >= 540 + 18,
                    M_start >= E_end + 9)
            ))
            if s3.check() == sat:
                m3 = s3.model()
                meetings = [
                    {"action": "meet", "person": "Melissa", 
                     "start_time": min_to_time(m3.eval(M_start).as_long()), 
                     "end_time": min_to_time(m3.eval(M_end).as_long())},
                    {"action": "meet", "person": "Emily", 
                     "start_time": min_to_time(m3.eval(E_start).as_long()), 
                     "end_time": min_to_time(m3.eval(E_end).as_long())}
                ]
                meetings_sorted = sorted(meetings, key=lambda x: x['start_time'])
                result = {'itinerary': meetings_sorted}
            else:
                s4 = Solver()
                s4.add(M_start >= 510, M_end <= 1200)
                s4.add(N_start >= 1185, N_end <= 1320)
                order_M4 = Int('order_M4')
                order_N4 = Int('order_N4')
                s4.add(order_M4 >= 0, order_M4 <= 1)
                s4.add(order_N4 >= 0, order_N4 <= 1)
                s4.add(Distinct(order_M4, order_N4))
                s4.add(Or(
                    And(order_M4 == 0, order_N4 == 1,
                        M_start >= 540 + 25,
                        N_start >= M_end + 11),
                    And(order_N4 == 0, order_M4 == 1,
                        N_start >= 540 + 17,
                        M_start >= N_end + 12)
                ))
                if s4.check() == sat:
                    m4 = s4.model()
                    meetings = [
                        {"action": "meet", "person": "Melissa", 
                         "start_time": min_to_time(m4.eval(M_start).as_long()), 
                         "end_time": min_to_time(m4.eval(M_end).as_long())},
                        {"action": "meet", "person": "Nancy", 
                         "start_time": min_to_time(m4.eval(N_start).as_long()), 
                         "end_time": min_to_time(m4.eval(N_end).as_long())}
                    ]
                    meetings_sorted = sorted(meetings, key=lambda x: x['start_time'])
                    result = {'itinerary': meetings_sorted}
                else:
                    result = {'itinerary': [
                        {"action": "meet", "person": "Melissa", "start_time": "09:25", "end_time": "09:40"}
                    ]}

    print(f"SOLUTION: {result}")

if __name__ == "__main__":
    main()