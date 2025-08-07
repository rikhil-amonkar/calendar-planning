import json
from itertools import permutations, combinations
from z3 import Int, Solver, sat

def main():
    # Define locations for each friend
    loc = {
        "Karen": "Fisherman's Wharf",
        "Anthony": "Financial District",
        "Betty": "Embarcadero"
    }
    
    # Define minimum meeting durations (in minutes)
    dur = {
        "Karen": 30,
        "Anthony": 105,
        "Betty": 15
    }
    
    # Define availability windows (start and end in minutes from midnight)
    avail = {
        "Karen": (8*60 + 45, 15*60),        # 8:45 AM to 3:00 PM
        "Anthony": (9*60 + 15, 21*60 + 30),  # 9:15 AM to 9:30 PM
        "Betty": (19*60 + 45, 21*60 + 45)    # 7:45 PM to 9:45 PM
    }
    
    # Define travel times between locations (in minutes)
    travel_times = {
        ("Bayview", "Embarcadero"): 19,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Financial District"): 19,
        ("Embarcadero", "Bayview"): 21,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Financial District"): 5,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Fisherman's Wharf"): 10
    }
    
    all_friends = ["Karen", "Anthony", "Betty"]
    result_itinerary = []
    
    # Try to meet 3 friends, then 2, then 1
    for n in [3, 2, 1]:
        found = False
        for subset in combinations(all_friends, n):
            for order in permutations(subset):
                s = Solver()
                starts = {}
                for friend in subset:
                    starts[friend] = Int(f'start_{friend}')
                
                # First meeting must start after traveling from Bayview
                first_friend = order[0]
                start_first = starts[first_friend]
                travel_from_bayview = travel_times[("Bayview", loc[first_friend])]
                s.add(start_first >= 540 + travel_from_bayview)
                
                # Chain constraints for subsequent meetings
                for i in range(1, len(order)):
                    prev_friend = order[i-1]
                    curr_friend = order[i]
                    tt = travel_times[(loc[prev_friend], loc[curr_friend])]
                    s.add(starts[curr_friend] >= starts[prev_friend] + dur[prev_friend] + tt)
                
                # Availability constraints
                for friend in subset:
                    s.add(starts[friend] >= avail[friend][0])
                    s.add(starts[friend] + dur[friend] <= avail[friend][1])
                
                # Check feasibility
                if s.check() == sat:
                    m = s.model()
                    meetings = []
                    for friend in subset:
                        start_val = m[starts[friend]].as_long()
                        end_val = start_val + dur[friend]
                        meetings.append((friend, start_val, end_val))
                    meetings_sorted = sorted(meetings, key=lambda x: x[1])
                    itinerary = []
                    for (friend, start_val, end_val) in meetings_sorted:
                        start_str = f"{start_val//60:02d}:{start_val%60:02d}"
                        end_str = f"{end_val//60:02d}:{end_val%60:02d}"
                        itinerary.append({
                            "action": "meet",
                            "person": friend,
                            "start_time": start_str,
                            "end_time": end_str
                        })
                    result_itinerary = itinerary
                    found = True
                    break
            if found:
                break
        if found:
            break
    
    solution_dict = {"itinerary": result_itinerary}
    print("SOLUTION:")
    print(json.dumps(solution_dict))

if __name__ == "__main__":
    main()