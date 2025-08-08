import json
from z3 import *

def main():
    travel_text = """
    The Castro to Marina District: 21.
    The Castro to Presidio: 20.
    The Castro to North Beach: 20.
    The Castro to Embarcadero: 22.
    The Castro to Haight-Ashbury: 6.
    The Castro to Golden Gate Park: 11.
    The Castro to Richmond District: 16.
    The Castro to Alamo Square: 8.
    The Castro to Financial District: 21.
    The Castro to Sunset District: 17.
    Marina District to The Castro: 22.
    Marina District to Presidio: 10.
    Marina District to North Beach: 11.
    Marina District to Embarcadero: 14.
    Marina District to Haight-Ashbury: 16.
    Marina District to Golden Gate Park: 18.
    Marina District to Richmond District: 11.
    Marina District to Alamo Square: 15.
    Marina District to Financial District: 17.
    Marina District to Sunset District: 19.
    Presidio to The Castro: 21.
    Presidio to Marina District: 10.
    Presidio to North Beach: 18.
    Presidio to Embarcadero: 20.
    Presidio to Haight-Ashbury: 15.
    Presidio to Golden Gate Park: 12.
    Presidio to Richmond District: 7.
    Presidio to Alamo Square: 19.
    Presidio to Financial District: 23.
    Presidio to Sunset District: 15.
    North Beach to The Castro: 23.
    North Beach to Marina District: 9.
    North Beach to Presidio: 17.
    North Beach to Embarcadero: 6.
    North Beach to Haight-Ashbury: 18.
    North Beach to Golden Gate Park: 22.
    North Beach to Richmond District: 18.
    North Beach to Alamo Square: 16.
    North Beach to Financial District: 8.
    North Beach to Sunset District: 27.
    Embarcadero to The Castro: 25.
    Embarcadero to Marina District: 12.
    Embarcadero to Presidio: 20.
    Embarcadero to North Beach: 5.
    Embarcadero to Haight-Ashbury: 21.
    Embarcadero to Golden Gate Park: 25.
    Embarcadero to Richmond District: 21.
    Embarcadero to Alamo Square: 19.
    Embarcadero to Financial District: 5.
    Embarcadero to Sunset District: 30.
    Haight-Ashbury to The Castro: 6.
    Haight-Ashbury to Marina District: 17.
    Haight-Ashbury to Presidio: 15.
    Haight-Ashbury to North Beach: 19.
    Haight-Ashbury to Embarcadero: 20.
    Haight-Ashbury to Golden Gate Park: 7.
    Haight-Ashbury to Richmond District: 10.
    Haight-Ashbury to Alamo Square: 5.
    Haight-Ashbury to Financial District: 21.
    Haight-Ashbury to Sunset District: 15.
    Golden Gate Park to The Castro: 13.
    Golden Gate Park to Marina District: 16.
    Golden Gate Park to Presidio: 11.
    Golden Gate Park to North Beach: 23.
    Golden Gate Park to Embarcadero: 25.
    Golden Gate Park to Haight-Ashbury: 7.
    Golden Gate Park to Richmond District: 7.
    Golden Gate Park to Alamo Square: 9.
    Golden Gate Park to Financial District: 26.
    Golden Gate Park to Sunset District: 10.
    Richmond District to The Castro: 16.
    Richmond District to Marina District: 9.
    Richmond District to Presidio: 7.
    Richmond District to North Beach: 17.
    Richmond District to Embarcadero: 19.
    Richmond District to Haight-Ashbury: 10.
    Richmond District to Golden Gate Park: 9.
    Richmond District to Alamo Square: 13.
    Richmond District to Financial District: 22.
    Richmond District to Sunset District: 11.
    Alamo Square to The Castro: 8.
    Alamo Square to Marina District: 15.
    Alamo Square to Presidio: 17.
    Alamo Square to North Beach: 15.
    Alamo Square to Embarcadero: 16.
    Alamo Square to Haight-Ashbury: 5.
    Alamo Square to Golden Gate Park: 9.
    Alamo Square to Richmond District: 11.
    Alamo Square to Financial District: 17.
    Alamo Square to Sunset District: 16.
    Financial District to The Castro: 20.
    Financial District to Marina District: 15.
    Financial District to Presidio: 22.
    Financial District to North Beach: 7.
    Financial District to Embarcadero: 4.
    Financial District to Haight-Ashbury: 19.
    Financial District to Golden Gate Park: 23.
    Financial District to Richmond District: 21.
    Financial District to Alamo Square: 17.
    Financial District to Sunset District: 30.
    Sunset District to The Castro: 17.
    Sunset District to Marina District: 21.
    Sunset District to Presidio: 16.
    Sunset District to North Beach: 28.
    Sunset District to Embarcadero: 30.
    Sunset District to Haight-Ashbury: 15.
    Sunset District to Golden Gate Park: 11.
    Sunset District to Richmond District: 12.
    Sunset District to Alamo Square: 17.
    Sunset District to Financial District: 30.
    """

    travel_dict = {}
    lines = travel_text.strip().split('\n')
    for line in lines:
        line = line.strip()
        if not line:
            continue
        if line.endswith('.'):
            line = line[:-1]
        parts = line.split(':')
        if len(parts) < 2:
            continue
        left_part = parts[0].strip()
        right_part = parts[1].strip().rstrip('.')
        try:
            time_val = int(right_part)
        except:
            continue
        if ' to ' not in left_part:
            continue
        locs = left_part.split(' to ')
        if len(locs) != 2:
            continue
        from_loc = locs[0].strip()
        to_loc = locs[1].strip()
        if from_loc not in travel_dict:
            travel_dict[from_loc] = {}
        travel_dict[from_loc][to_loc] = time_val

    friends = [
        ("Elizabeth", "Marina District", 19*60, 20*60+45, 105),
        ("Joshua", "Presidio", 8*60+30, 13*60+15, 105),
        ("Timothy", "North Beach", 19*60+45, 22*60, 90),
        ("David", "Embarcadero", 10*60+45, 12*60+30, 30),
        ("Kimberly", "Haight-Ashbury", 16*60+45, 21*60+30, 75),
        ("Lisa", "Golden Gate Park", 17*60+30, 21*60+45, 45),
        ("Ronald", "Richmond District", 8*60, 9*60+30, 90),
        ("Stephanie", "Alamo Square", 15*60+30, 16*60+30, 30),
        ("Helen", "Financial District", 17*60+30, 18*60+30, 45),
        ("Laura", "Sunset District", 17*60+45, 21*60+15, 90),
    ]

    s = Optimize()
    s.set("timeout", 300000)

    meet_vars = {}
    start_vars = {}
    end_vars = {}
    order_vars = {}

    for (name, loc, avail_start, avail_end, min_dur) in friends:
        meet_vars[name] = Bool(f"meet_{name}")
        start_vars[name] = Int(f"start_{name}")
        end_vars[name] = Int(f"end_{name}")
        order_vars[name] = Int(f"order_{name}")

    k = Int('k')
    s.add(k == Sum([If(meet_vars[name], 1, 0) for name, _, _, _, _ in friends]))

    for (name, loc, avail_start, avail_end, min_dur) in friends:
        s.add(Implies(meet_vars[name], start_vars[name] >= avail_start))
        s.add(Implies(meet_vars[name], end_vars[name] <= avail_end))
        s.add(Implies(meet_vars[name], end_vars[name] - start_vars[name] >= min_dur))
        s.add(Implies(meet_vars[name], order_vars[name] >= 0))
        s.add(Implies(meet_vars[name], order_vars[name] < k))

    for i in range(len(friends)):
        name_i = friends[i][0]
        for j in range(i+1, len(friends)):
            name_j = friends[j][0]
            s.add(Implies(And(meet_vars[name_i], meet_vars[name_j]), order_vars[name_i] != order_vars[name_j]))

    for (name, loc, avail_start, avail_end, min_dur) in friends:
        s.add(Implies(And(meet_vars[name], order_vars[name] == 0), 
                     start_vars[name] >= 540 + travel_dict['The Castro'][loc]))

    for i in range(len(friends)):
        name_i = friends[i][0]
        loc_i = friends[i][1]
        for j in range(len(friends)):
            if i == j:
                continue
            name_j = friends[j][0]
            loc_j = friends[j][1]
            s.add(Implies(
                And(meet_vars[name_i], meet_vars[name_j], order_vars[name_j] == order_vars[name_i] - 1),
                start_vars[name_i] >= end_vars[name_j] + travel_dict[loc_j][loc_i]
            ))

    s.maximize(k)

    if s.check() == sat:
        model = s.model()
        k_val = model.eval(k).as_long()
        itinerary = []
        for (name, loc, avail_start, avail_end, min_dur) in friends:
            if model.eval(meet_vars[name]):
                start_val = model.eval(start_vars[name]).as_long()
                end_val = model.eval(end_vars[name]).as_long()
                start_hour = start_val // 60
                start_minute = start_val % 60
                end_hour = end_val // 60
                end_minute = end_val % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_str,
                    "end_time": end_str
                })
        order_list = []
        for (name, loc, avail_start, avail_end, min_dur) in friends:
            if model.eval(meet_vars[name]):
                order_val = model.eval(order_vars[name]).as_long()
                order_list.append((order_val, name))
        order_list.sort(key=lambda x: x[0])
        sorted_itinerary = []
        for order_val, name in order_list:
            for entry in itinerary:
                if entry['person'] == name:
                    sorted_itinerary.append(entry)
                    break
        result = {"itinerary": sorted_itinerary}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()