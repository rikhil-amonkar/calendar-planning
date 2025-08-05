from z3 import *

def min_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def main():
    travel_times = {
        ('S', 'N'): 29,
        ('S', 'U'): 30,
        ('S', 'A'): 17,
        ('N', 'S'): 27,
        ('N', 'U'): 7,
        ('N', 'A'): 16,
        ('U', 'S'): 26,
        ('U', 'N'): 10,
        ('U', 'A'): 15,
        ('A', 'S'): 16,
        ('A', 'N'): 15,
        ('A', 'U'): 14
    }

    s = Optimize()

    meet_s = Bool('meet_s')
    meet_j = Bool('meet_j')
    meet_b = Bool('meet_b')

    s_s = Int('s_s')
    e_s = Int('e_s')
    s_j = Int('s_j')
    e_j = Int('e_j')
    s_b = Int('s_b')
    e_b = Int('e_b')

    s.add(Implies(meet_s, s_s >= 960))
    s.add(Implies(meet_s, e_s <= 1095))
    s.add(Implies(meet_s, e_s - s_s >= 60))

    s.add(Implies(meet_j, s_j >= 900))
    s.add(Implies(meet_j, e_j <= 1320))
    s.add(Implies(meet_j, e_j - s_j >= 75))

    s.add(Implies(meet_b, s_b >= 960))
    s.add(Implies(meet_b, s_b <= 975))
    s.add(Implies(meet_b, e_b - s_b >= 75))

    s.add(Implies(meet_s, 
                Or(
                    s_s >= 540 + travel_times[('S','N')],
                    And(meet_j, s_s >= e_j + travel_times[('U','N')]),
                    And(meet_b, s_s >= e_b + travel_times[('A','N')])
                )))

    s.add(Implies(meet_j,
                Or(
                    s_j >= 540 + travel_times[('S','U')],
                    And(meet_s, s_j >= e_s + travel_times[('N','U')]),
                    And(meet_b, s_j >= e_b + travel_times[('A','U')])
                )))

    s.add(Implies(meet_b,
                Or(
                    s_b >= 540 + travel_times[('S','A')],
                    And(meet_s, s_b >= e_s + travel_times[('N','A')]),
                    And(meet_j, s_b >= e_j + travel_times[('U','A')])
                )))

    s.add(Implies(And(meet_s, meet_j),
                Or( s_j >= e_s + travel_times[('N','U')], 
                    s_s >= e_j + travel_times[('U','N')] )))

    s.add(Implies(And(meet_s, meet_b),
                Or( s_b >= e_s + travel_times[('N','A')], 
                    s_s >= e_b + travel_times[('A','N')] )))

    s.add(Implies(And(meet_j, meet_b),
                Or( s_b >= e_j + travel_times[('U','A')], 
                    s_j >= e_b + travel_times[('A','U')] )))

    s.maximize(If(meet_s, 1, 0) + If(meet_j, 1, 0) + If(meet_b, 1, 0))

    if s.check() == sat:
        model = s.model()
        itinerary = []
        if is_true(model[meet_s]):
            start_s = model[s_s].as_long()
            end_s = model[e_s].as_long()
            itinerary.append({
                "action": "meet",
                "person": "Sarah",
                "start_time": min_to_time(start_s),
                "end_time": min_to_time(end_s)
            })
        if is_true(model[meet_j]):
            start_j = model[s_j].as_long()
            end_j = model[e_j].as_long()
            itinerary.append({
                "action": "meet",
                "person": "Jeffrey",
                "start_time": min_to_time(start_j),
                "end_time": min_to_time(end_j)
            })
        if is_true(model[meet_b]):
            start_b = model[s_b].as_long()
            end_b = model[e_b].as_long()
            itinerary.append({
                "action": "meet",
                "person": "Brian",
                "start_time": min_to_time(start_b),
                "end_time": min_to_time(end_b)
            })
        itinerary.sort(key=lambda x: x['start_time'])
        print({"itinerary": itinerary})
    else:
        print({"itinerary": []})

if __name__ == "__main__":
    main()