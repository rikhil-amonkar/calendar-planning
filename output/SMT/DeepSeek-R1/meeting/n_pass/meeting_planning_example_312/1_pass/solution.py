from z3 import *
import json

def main():
    # Initialize the solver with optimization
    s = Optimize()
    
    # Define whether we meet each friend
    meet_Sarah = Bool('meet_Sarah')
    meet_Richard = Bool('meet_Richard')
    meet_Elizabeth = Bool('meet_Elizabeth')
    meet_Michelle = Bool('meet_Michelle')
    
    # Define start and end times for each friend (in minutes from 9:00 AM)
    start_Sarah = Real('start_Sarah')
    end_Sarah = Real('end_Sarah')
    start_Richard = Real('start_Richard')
    end_Richard = Real('end_Richard')
    start_Elizabeth = Real('start_Elizabeth')
    end_Elizabeth = Real('end_Elizabeth')
    start_Michelle = Real('start_Michelle')
    end_Michelle = Real('end_Michelle')
    
    # Convert availability times to minutes from 9:00 AM
    # Sarah: 10:45 AM to 7:00 PM -> (10-9)*60+45 = 105, (19-9)*60 = 600
    s.add(Implies(meet_Sarah, start_Sarah >= 105))
    s.add(Implies(meet_Sarah, end_Sarah == start_Sarah + 30))
    s.add(Implies(meet_Sarah, end_Sarah <= 600))
    
    # Richard: 11:45 AM to 3:45 PM -> (11-9)*60+45=165, (15-9)*60+45=405
    s.add(Implies(meet_Richard, start_Richard >= 165))
    s.add(Implies(meet_Richard, end_Richard == start_Richard + 90))
    s.add(Implies(meet_Richard, end_Richard <= 405))
    
    # Elizabeth: 11:00 AM to 5:15 PM -> (11-9)*60=120, (17-9)*60+15=495
    s.add(Implies(meet_Elizabeth, start_Elizabeth >= 120))
    s.add(Implies(meet_Elizabeth, end_Elizabeth == start_Elizabeth + 120))
    s.add(Implies(meet_Elizabeth, end_Elizabeth <= 495))
    
    # Michelle: 6:15 PM to 8:45 PM -> (18-9)*60+15=555, (20-9)*60+45=705
    s.add(Implies(meet_Michelle, start_Michelle >= 555))
    s.add(Implies(meet_Michelle, end_Michelle == start_Michelle + 90))
    s.add(Implies(meet_Michelle, end_Michelle <= 705))
    
    # Travel time dictionary
    travel_time_dict = {
        "Richmond District": {
            "Sunset District": 11,
            "Haight-Ashbury": 10,
            "Mission District": 20,
            "Golden Gate Park": 9
        },
        "Sunset District": {
            "Richmond District": 12,
            "Haight-Ashbury": 15,
            "Mission District": 24,
            "Golden Gate Park": 11
        },
        "Haight-Ashbury": {
            "Richmond District": 10,
            "Sunset District": 15,
            "Mission District": 11,
            "Golden Gate Park": 7
        },
        "Mission District": {
            "Richmond District": 20,
            "Sunset District": 24,
            "Haight-Ashbury": 12,
            "Golden Gate Park": 17
        },
        "Golden Gate Park": {
            "Richmond District": 7,
            "Sunset District": 10,
            "Haight-Ashbury": 7,
            "Mission District": 17
        }
    }
    
    # Locations for each friend
    locations = {
        "Sarah": "Sunset District",
        "Richard": "Haight-Ashbury",
        "Elizabeth": "Mission District",
        "Michelle": "Golden Gate Park"
    }
    
    # Constraints for travel from Richmond to each meeting
    s.add(Implies(meet_Sarah, start_Sarah >= travel_time_dict["Richmond District"][locations["Sarah"]]))
    s.add(Implies(meet_Richard, start_Richard >= travel_time_dict["Richmond District"][locations["Richard"]]))
    s.add(Implies(meet_Elizabeth, start_Elizabeth >= travel_time_dict["Richmond District"][locations["Elizabeth"]]))
    s.add(Implies(meet_Michelle, start_Michelle >= travel_time_dict["Richmond District"][locations["Michelle"]]))
    
    # Friends dictionary for iteration
    friends = {
        "Sarah": (meet_Sarah, start_Sarah, end_Sarah, locations["Sarah"]),
        "Richard": (meet_Richard, start_Richard, end_Richard, locations["Richard"]),
        "Elizabeth": (meet_Elizabeth, start_Elizabeth, end_Elizabeth, locations["Elizabeth"]),
        "Michelle": (meet_Michelle, start_Michelle, end_Michelle, locations["Michelle"])
    }
    
    # Pairwise constraints for travel between meetings
    friend_names = list(friends.keys())
    for i in range(len(friend_names)):
        for j in range(i+1, len(friend_names)):
            name_i = friend_names[i]
            name_j = friend_names[j]
            meet_i, start_i, end_i, loc_i = friends[name_i]
            meet_j, start_j, end_j, loc_j = friends[name_j]
            both_meet = And(meet_i, meet_j)
            travel_time_ij = travel_time_dict[loc_i][loc_j]
            travel_time_ji = travel_time_dict[loc_j][loc_i]
            constraint = Or(
                end_i + travel_time_ij <= start_j,
                end_j + travel_time_ji <= start_i
            )
            s.add(Implies(both_meet, constraint))
    
    # Maximize the total number of meetings
    total_meetings = Sum([If(meet_var, 1, 0) for meet_var in [meet_Sarah, meet_Richard, meet_Elizabeth, meet_Michelle]])
    s.maximize(total_meetings)
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for name in friend_names:
            meet_var, start_var, end_var, loc = friends[name]
            if is_true(m[meet_var]):
                start_val = m[start_var]
                end_val = m[end_var]
                if is_int_value(start_val) and is_int_value(end_val):
                    start_minutes = start_val.as_long()
                    end_minutes = end_val.as_long()
                else:
                    start_minutes = int(start_val.as_fraction().numerator / start_val.as_fraction().denominator)
                    end_minutes = int(end_val.as_fraction().numerator / end_val.as_fraction().denominator)
                total_minutes_start = start_minutes
                hour_start = 9 + total_minutes_start // 60
                minute_start = total_minutes_start % 60
                start_time = f"{hour_start:02d}:{minute_start:02d}"
                total_minutes_end = end_minutes
                hour_end = 9 + total_minutes_end // 60
                minute_end = total_minutes_end % 60
                end_time = f"{hour_end:02d}:{minute_end:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result, indent=4))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}, indent=4))

if __name__ == "__main__":
    main()