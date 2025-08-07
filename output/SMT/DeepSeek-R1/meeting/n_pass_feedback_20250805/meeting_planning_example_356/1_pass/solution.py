from z3 import *
import json

def main():
    friends = [
        ("Barbara", "North Beach", 825, 1215, 60),
        ("Margaret", "Presidio", 615, 915, 30),
        ("Kevin", "Haight-Ashbury", 1200, 1245, 30),
        ("Kimberly", "Union Square", 465, 1005, 30)
    ]

    travel_dict = {
        ("Bayview", "North Beach"): 21,
        ("Bayview", "Presidio"): 31,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Union Square"): 17,
        ("North Beach", "Bayview"): 22,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Union Square"): 7,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Union Square"): 22,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Union Square"): 17,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Haight-Ashbury"): 18
    }

    meet_vars = {}
    start_vars = {}
    end_vars = {}
    for name, loc, avail_start, avail_end, min_dur in friends:
        meet_vars[name] = Bool('meet_' + name)
        start_vars[name] = Int('start_' + name)
        end_vars[name] = Int('end_' + name)

    o = Optimize()
    
    for name, loc, avail_start, avail_end, min_dur in friends:
        o.add(Implies(meet_vars[name], 
                      And(
                          start_vars[name] >= avail_start,
                          end_vars[name] == start_vars[name] + min_dur,
                          end_vars[name] <= avail_end,
                          start_vars[name] >= 540 + travel_dict[("Bayview", loc)]
                      )))
    
    from itertools import combinations
    pairs = list(combinations(friends, 2))
    for (name1, loc1, avail_start1, avail_end1, min_dur1), (name2, loc2, avail_start2, avail_end2, min_dur2) in pairs:
        travel_1to2 = travel_dict[(loc1, loc2)]
        travel_2to1 = travel_dict[(loc2, loc1)]
        o.add(Implies(And(meet_vars[name1], meet_vars[name2]),
                      Or( 
                          start_vars[name1] + min_dur1 + travel_1to2 <= start_vars[name2],
                          start_vars[name2] + min_dur2 + travel_2to1 <= start_vars[name1]
                      )))
    
    total_meetings = Sum([If(meet_vars[name], 1, 0) for name in meet_vars])
    o.maximize(total_meetings)
    
    if o.check() == sat:
        m = o.model()
        itinerary = []
        for name in meet_vars:
            if m.evaluate(meet_vars[name]):
                start_val = m.evaluate(start_vars[name]).as_long()
                end_val = m.evaluate(end_vars[name]).as_long()
                start_hour = start_val // 60
                start_minute = start_val % 60
                end_hour = end_val // 60
                end_minute = end_val % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({"action": "meet", "person": name, "start_time": start_str, "end_time": end_str})
        itinerary.sort(key=lambda x: x['start_time'])
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result, separators=(',', ':')))
    else:
        print("SOLUTION:")
        print('{"itinerary":[]}')

if __name__ == "__main__":
    main()