from z3 import *

def main():
    locations = [
        "Nob Hill",
        "Embarcadero",
        "The Castro",
        "Haight-Ashbury",
        "Union Square",
        "North Beach",
        "Pacific Heights",
        "Chinatown",
        "Golden Gate Park",
        "Marina District",
        "Russian Hill"
    ]
    loc_to_index = {loc: idx for idx, loc in enumerate(locations)}
    
    T = [[0]*11 for _ in range(11)]
    
    travel_text = """
Nob Hill to Embarcadero: 9.
Nob Hill to The Castro: 17.
Nob Hill to Haight-Ashbury: 13.
Nob Hill to Union Square: 7.
Nob Hill to North Beach: 8.
Nob Hill to Pacific Heights: 8.
Nob Hill to Chinatown: 6.
Nob Hill to Golden Gate Park: 17.
Nob Hill to Marina District: 11.
Nob Hill to Russian Hill: 5.
Embarcadero to Nob Hill: 10.
Embarcadero to The Castro: 25.
Embarcadero to Haight-Ashbury: 21.
Embarcadero to Union Square: 10.
Embarcadero to North Beach: 5.
Embarcadero to Pacific Heights: 11.
Embarcadero to Chinatown: 7.
Embarcadero to Golden Gate Park: 25.
Embarcadero to Marina District: 12.
Embarcadero to Russian Hill: 8.
The Castro to Nob Hill: 16.
The Castro to Embarcadero: 22.
The Castro to Haight-Ashbury: 6.
The Castro to Union Square: 19.
The Castro to North Beach: 20.
The Castro to Pacific Heights: 16.
The Castro to Chinatown: 22.
The Castro to Golden Gate Park: 11.
The Castro to Marina District: 21.
The Castro to Russian Hill: 18.
Haight-Ashbury to Nob Hill: 15.
Haight-Ashbury to Embarcadero: 20.
Haight-Ashbury to The Castro: 6.
Haight-Ashbury to Union Square: 19.
Haight-Ashbury to North Beach: 19.
Haight-Ashbury to Pacific Heights: 12.
Haight-Ashbury to Chinatown: 19.
Haight-Ashbury to Golden Gate Park: 7.
Haight-Ashbury to Marina District: 17.
Haight-Ashbury to Russian Hill: 17.
Union Square to Nob Hill: 9.
Union Square to Embarcadero: 11.
Union Square to The Castro: 17.
Union Square to Haight-Ashbury: 18.
Union Square to North Beach: 10.
Union Square to Pacific Heights: 15.
Union Square to Chinatown: 7.
Union Square to Golden Gate Park: 22.
Union Square to Marina District: 18.
Union Square to Russian Hill: 13.
North Beach to Nob Hill: 7.
North Beach to Embarcadero: 6.
North Beach to The Castro: 23.
North Beach to Haight-Ashbury: 18.
North Beach to Union Square: 7.
North Beach to Pacific Heights: 8.
North Beach to Chinatown: 6.
North Beach to Golden Gate Park: 22.
North Beach to Marina District: 9.
North Beach to Russian Hill: 4.
Pacific Heights to Nob Hill: 8.
Pacific Heights to Embarcadero: 10.
Pacific Heights to The Castro: 16.
Pacific Heights to Haight-Ashbury: 11.
Pacific Heights to Union Square: 12.
Pacific Heights to North Beach: 9.
Pacific Heights to Chinatown: 11.
Pacific Heights to Golden Gate Park: 15.
Pacific Heights to Marina District: 6.
Pacific Heights to Russian Hill: 7.
Chinatown to Nob Hill: 9.
Chinatown to Embarcadero: 5.
Chinatown to The Castro: 22.
Chinatown to Haight-Ashbury: 19.
Chinatown to Union Square: 7.
Chinatown to North Beach: 3.
Chinatown to Pacific Heights: 10.
Chinatown to Golden Gate Park: 23.
Chinatown to Marina District: 12.
Chinatown to Russian Hill: 7.
Golden Gate Park to Nob Hill: 20.
Golden Gate Park to Embarcadero: 25.
Golden Gate Park to The Castro: 13.
Golden Gate Park to Haight-Ashbury: 7.
Golden Gate Park to Union Square: 22.
Golden Gate Park to North Beach: 23.
Golden Gate Park to Pacific Heights: 16.
Golden Gate Park to Chinatown: 23.
Golden Gate Park to Marina District: 16.
Golden Gate Park to Russian Hill: 19.
Marina District to Nob Hill: 12.
Marina District to Embarcadero: 14.
Marina District to The Castro: 22.
Marina District to Haight-Ashbury: 16.
Marina District to Union Square: 16.
Marina District to North Beach: 11.
Marina District to Pacific Heights: 7.
Marina District to Chinatown: 15.
Marina District to Golden Gate Park: 18.
Marina District to Russian Hill: 8.
Russian Hill to Nob Hill: 5.
Russian Hill to Embarcadero: 8.
Russian Hill to The Castro: 21.
Russian Hill to Haight-Ashbury: 17.
Russian Hill to Union Square: 10.
Russian Hill to North Beach: 5.
Russian Hill to Pacific Heights: 7.
Russian Hill to Chinatown: 9.
Russian Hill to Golden Gate Park: 21.
Russian Hill to Marina District: 7.
    """
    lines = travel_text.strip().split('\n')
    for line in lines:
        line = line.strip()
        if not line:
            continue
        parts = line.split(':')
        time_str = parts[1].strip().rstrip('.')
        time_val = int(time_str)
        locs_str = parts[0].strip()
        if " to " in locs_str:
            from_loc, to_loc = locs_str.split(" to ")
            from_loc = from_loc.strip()
            to_loc = to_loc.strip()
            i = loc_to_index[from_loc]
            j = loc_to_index[to_loc]
            T[i][j] = time_val

    friends = [
        ("Mary", "Embarcadero", 660, 735, 75),
        ("Kenneth", "The Castro", 135, 615, 30),
        ("Joseph", "Haight-Ashbury", 660, 780, 120),
        ("Sarah", "Union Square", 165, 330, 90),
        ("Thomas", "North Beach", 615, 645, 15),
        ("Daniel", "Pacific Heights", 285, 690, 15),
        ("Richard", "Chinatown", -60, 585, 30),
        ("Mark", "Golden Gate Park", 510, 750, 120),
        ("David", "Marina District", 660, 720, 60),
        ("Karen", "Russian Hill", 255, 570, 120)
    ]
    loc_indices = [loc_to_index[friend[1]] for friend in friends]

    s = Solver()
    n = len(friends)
    meet = [Bool(f"meet_{i}") for i in range(n)]
    start = [Int(f"start_{i}") for i in range(n)]

    for i in range(n):
        s.add(Implies(meet[i], start[i] >= friends[i][2]))
        s.add(Implies(meet[i], start[i] + friends[i][4] <= friends[i][3]))
        s.add(Implies(meet[i], start[i] >= T[0][loc_indices[i]]))

    for i in range(n):
        for j in range(i+1, n):
            constraint = Or(
                start[j] >= start[i] + friends[i][4] + T[loc_indices[i]][loc_indices[j]],
                start[i] >= start[j] + friends[j][4] + T[loc_indices[j]][loc_indices[i]]
            )
            s.add(Implies(And(meet[i], meet[j]), constraint))

    obj = Sum([If(meet[i], 1, 0) for i in range(n)])
    s.maximize(obj)

    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n):
            if is_true(m.eval(meet[i])):
                t_val = m.eval(start[i])
                if isinstance(t_val, IntNumRef):
                    total_minutes = t_val.as_long()
                else:
                    total_minutes = t_val
                hours = 9 + total_minutes // 60
                minutes = total_minutes % 60
                if hours < 12:
                    time_str = f"{hours}:{minutes:02d}AM"
                elif hours == 12:
                    time_str = f"12:{minutes:02d}PM"
                else:
                    time_str = f"{hours-12}:{minutes:02d}PM"
                itinerary.append({
                    'friend': friends[i][0],
                    'location': friends[i][1],
                    'start_time': time_str,
                    'duration': friends[i][4]
                })
        itinerary.sort(key=lambda x: (int(x['start_time'].split(':')[0].strip('APM'), 
                                      int(x['start_time'].split(':')[1][:2].strip('APM'))))
        print("SOLUTION:")
        print(f"Total meetings: {len(itinerary)}")
        for item in itinerary:
            print(f"Meet {item['friend']} at {item['location']} starting at {item['start_time']} for {item['duration']} minutes.")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()