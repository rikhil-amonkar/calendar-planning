import json
from z3 import *

def main():
    # Travel time data: list of (from, to, time) tuples
    travel_data = [
        ("Sunset District", "Presidio", 16),
        ("Sunset District", "Nob Hill", 27),
        ("Sunset District", "Pacific Heights", 21),
        ("Sunset District", "Mission District", 25),
        ("Sunset District", "Marina District", 21),
        ("Sunset District", "North Beach", 28),
        ("Sunset District", "Russian Hill", 24),
        ("Sunset District", "Richmond District", 12),
        ("Sunset District", "Embarcadero", 30),
        ("Sunset District", "Alamo Square", 17),
        ("Presidio", "Sunset District", 15),
        ("Presidio", "Nob Hill", 18),
        ("Presidio", "Pacific Heights", 11),
        ("Presidio", "Mission District", 26),
        ("Presidio", "Marina District", 11),
        ("Presidio", "North Beach", 18),
        ("Presidio", "Russian Hill", 14),
        ("Presidio", "Richmond District", 7),
        ("Presidio", "Embarcadero", 20),
        ("Presidio", "Alamo Square", 19),
        ("Nob Hill", "Sunset District", 24),
        ("Nob Hill", "Presidio", 17),
        ("Nob Hill", "Pacific Heights", 8),
        ("Nob Hill", "Mission District", 13),
        ("Nob Hill", "Marina District", 11),
        ("Nob Hill", "North Beach", 8),
        ("Nob Hill", "Russian Hill", 5),
        ("Nob Hill", "Richmond District", 14),
        ("Nob Hill", "Embarcadero", 9),
        ("Nob Hill", "Alamo Square", 11),
        ("Pacific Heights", "Sunset District", 21),
        ("Pacific Heights", "Presidio", 11),
        ("Pacific Heights", "Nob Hill", 8),
        ("Pacific Heights", "Mission District", 15),
        ("Pacific Heights", "Marina District", 6),
        ("Pacific Heights", "North Beach", 9),
        ("Pacific Heights", "Russian Hill", 7),
        ("Pacific Heights", "Richmond District", 12),
        ("Pacific Heights", "Embarcadero", 10),
        ("Pacific Heights", "Alamo Square", 10),
        ("Mission District", "Sunset District", 24),
        ("Mission District", "Presidio", 25),
        ("Mission District", "Nob Hill", 12),
        ("Mission District", "Pacific Heights", 16),
        ("Mission District", "Marina District", 19),
        ("Mission District", "North Beach", 17),
        ("Mission District", "Russian Hill", 15),
        ("Mission District", "Richmond District", 20),
        ("Mission District", "Embarcadero", 19),
        ("Mission District", "Alamo Square", 11),
        ("Marina District", "Sunset District", 19),
        ("Marina District", "Presidio", 10),
        ("Marina District", "Nob Hill", 12),
        ("Marina District", "Pacific Heights", 7),
        ("Marina District", "Mission District", 20),
        ("Marina District", "North Beach", 11),
        ("Marina District", "Russian Hill", 8),
        ("Marina District", "Richmond District", 11),
        ("Marina District", "Embarcadero", 14),
        ("Marina District", "Alamo Square", 15),
        ("North Beach", "Sunset District", 27),
        ("North Beach", "Presidio", 17),
        ("North Beach", "Nob Hill", 7),
        ("North Beach", "Pacific Heights", 8),
        ("North Beach", "Mission District", 18),
        ("North Beach", "Marina District", 9),
        ("North Beach", "Russian Hill", 4),
        ("North Beach", "Richmond District", 18),
        ("North Beach", "Embarcadero", 6),
        ("North Beach", "Alamo Square", 16),
        ("Russian Hill", "Sunset District", 23),
        ("Russian Hill", "Presidio", 14),
        ("Russian Hill", "Nob Hill", 5),
        ("Russian Hill", "Pacific Heights", 7),
        ("Russian Hill", "Mission District", 16),
        ("Russian Hill", "Marina District", 7),
        ("Russian Hill", "North Beach", 5),
        ("Russian Hill", "Richmond District", 14),
        ("Russian Hill", "Embarcadero", 8),
        ("Russian Hill", "Alamo Square", 15),
        ("Richmond District", "Sunset District", 11),
        ("Richmond District", "Presidio", 7),
        ("Richmond District", "Nob Hill", 17),
        ("Richmond District", "Pacific Heights", 10),
        ("Richmond District", "Mission District", 20),
        ("Richmond District", "Marina District", 9),
        ("Richmond District", "North Beach", 17),
        ("Richmond District", "Russian Hill", 13),
        ("Richmond District", "Embarcadero", 19),
        ("Richmond District", "Alamo Square", 13),
        ("Embarcadero", "Sunset District", 30),
        ("Embarcadero", "Presidio", 20),
        ("Embarcadero", "Nob Hill", 10),
        ("Embarcadero", "Pacific Heights", 11),
        ("Embarcadero", "Mission District", 20),
        ("Embarcadero", "Marina District", 12),
        ("Embarcadero", "North Beach", 5),
        ("Embarcadero", "Russian Hill", 8),
        ("Embarcadero", "Richmond District", 21),
        ("Embarcadero", "Alamo Square", 19),
        ("Alamo Square", "Sunset District", 16),
        ("Alamo Square", "Presidio", 17),
        ("Alamo Square", "Nob Hill", 11),
        ("Alamo Square", "Pacific Heights", 10),
        ("Alamo Square", "Mission District", 10),
        ("Alamo Square", "Marina District", 15),
        ("Alamo Square", "North Beach", 15),
        ("Alamo Square", "Russian Hill", 13),
        ("Alamo Square", "Richmond District", 11),
        ("Alamo Square", "Embarcadero", 16)
    ]

    travel_time_dict = {}
    for (f, t, time) in travel_data:
        travel_time_dict[(f, t)] = time

    friends = ["Charles", "Robert", "Nancy", "Brian", "Kimberly", "David", "William", "Jeffrey", "Karen", "Joshua"]
    
    locations = {
        "Charles": "Presidio",
        "Robert": "Nob Hill",
        "Nancy": "Pacific Heights",
        "Brian": "Mission District",
        "Kimberly": "Marina District",
        "David": "North Beach",
        "William": "Russian Hill",
        "Jeffrey": "Richmond District",
        "Karen": "Embarcadero",
        "Joshua": "Alamo Square"
    }
    
    min_duration = {
        "Charles": 105,
        "Robert": 90,
        "Nancy": 105,
        "Brian": 60,
        "Kimberly": 75,
        "David": 75,
        "William": 120,
        "Jeffrey": 45,
        "Karen": 60,
        "Joshua": 60
    }
    
    availability_start = {
        "Charles": 13*60+15,   # 1:15PM -> 795
        "Robert": 13*60+15,     # 795
        "Nancy": 14*60+45,      # 885
        "Brian": 15*60+30,      # 930
        "Kimberly": 17*60,      # 1020
        "David": 14*60+45,      # 885
        "William": 12*60+30,    # 750
        "Jeffrey": 12*60,       # 720
        "Karen": 14*60+15,      # 855
        "Joshua": 18*60+45      # 1125
    }
    
    availability_end = {
        "Charles": 15*60,       # 3:00PM -> 900
        "Robert": 17*60+30,     # 5:30PM -> 1050
        "Nancy": 22*60,         # 10:00PM -> 1320
        "Brian": 22*60,         # 1320
        "Kimberly": 19*60+45,   # 7:45PM -> 1185
        "David": 16*60+30,      # 4:30PM -> 990
        "William": 19*60+15,    # 7:15PM -> 1155
        "Jeffrey": 19*60+15,    # 1155
        "Karen": 20*60+45,      # 8:45PM -> 1245
        "Joshua": 22*60         # 10:00PM -> 1320
    }
    
    s = Optimize()
    
    b = { friend: Bool(f"b_{friend}") for friend in friends }
    start = { friend: Int(f"start_{friend}") for friend in friends }
    end = { friend: start[friend] + min_duration[friend] }
    
    # Constraints for each friend if they are met
    for friend in friends:
        loc = locations[friend]
        travel_from_sunset = travel_time_dict[("Sunset District", loc)]
        s.add(Implies(b[friend], start[friend] >= availability_start[friend]))
        s.add(Implies(b[friend], end[friend] <= availability_end[friend]))
        s.add(Implies(b[friend], start[friend] >= 540 + travel_from_sunset))  # 540 is 9:00AM in minutes
    
    # Disjunctive constraints for every pair of friends
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            friend_i = friends[i]
            friend_j = friends[j]
            loc_i = locations[friend_i]
            loc_j = locations[friend_j]
            travel_i_j = travel_time_dict[(loc_i, loc_j)]
            travel_j_i = travel_time_dict[(loc_j, loc_i)]
            
            constraint = Or(
                end[friend_i] + travel_i_j <= start[friend_j],
                end[friend_j] + travel_j_i <= start[friend_i]
            )
            s.add(Implies(And(b[friend_i], b[friend_j]), constraint))
    
    total_meetings = Sum([If(b[friend], 1, 0) for friend in friends])
    s.maximize(total_meetings)
    
    if s.check() == sat:
        m = s.model()
        schedule = []
        for friend in friends:
            if m.eval(b[friend]):
                s_val = m.eval(start[friend])
                if isinstance(s_val, IntNumRef):
                    s_val = s_val.as_long()
                else:
                    s_val = s_val
                e_val = s_val + min_duration[friend]
                start_hour = s_val // 60
                start_minute = s_val % 60
                end_hour = e_val // 60
                end_minute = e_val % 60
                schedule.append({
                    "action": "meet",
                    "person": friend,
                    "start_time": f"{start_hour:02d}:{start_minute:02d}",
                    "end_time": f"{end_hour:02d}:{end_minute:02d}"
                })
        schedule.sort(key=lambda x: (x['start_time']))
        result = {"itinerary": schedule}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()