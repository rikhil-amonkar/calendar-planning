import json
from z3 import *

def minutes_to_time(m):
    # Convert minutes (integer) to a string in H:MM 24-hour format (e.g., 9:00, 21:30)
    h = m // 60
    minute = m % 60
    return f"{h}:{minute:02d}"

def main():
    # Define travel times (in minutes) as provided.
    travel_times = {
        ("Fisherman's Wharf", "The Castro"): 26,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Alamo Square"): 20,
        ("Fisherman's Wharf", "North Beach"): 6,

        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "North Beach"): 20,

        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "North Beach"): 24,

        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "North Beach"): 5,

        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "North Beach"): 5,

        ("Nob Hill", "Fisherman's Wharf"): 11,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "North Beach"): 8,

        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Embarcadero"): 17,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "North Beach"): 15,

        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "The Castro"): 22,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Alamo Square"): 16
    }
    
    # Meeting data for each friend.
    # Times are in minutes from midnight.
    # Fisherman's Wharf arrival is fixed at 9:00 AM (540 minutes).
    meetings_data = [
        {"person": "Laura", "location": "The Castro", "avail_start": 19*60 + 45, "avail_end": 21*60 + 30, "min_duration": 105},   # 19:45 to 21:30
        {"person": "Daniel", "location": "Golden Gate Park", "avail_start": 21*60 + 15, "avail_end": 21*60 + 45, "min_duration": 15},  # 21:15 to 21:45
        {"person": "William", "location": "Embarcadero", "avail_start": 7*60, "avail_end": 9*60, "min_duration": 90},                     # 7:00 to 9:00
        {"person": "Karen", "location": "Russian Hill", "avail_start": 14*60 + 30, "avail_end": 19*60 + 45, "min_duration": 30},         # 14:30 to 19:45
        {"person": "Stephanie", "location": "Nob Hill", "avail_start": 7*60 + 30, "avail_end": 9*60 + 30, "min_duration": 45},            # 7:30 to 9:30
        {"person": "Joseph", "location": "Alamo Square", "avail_start": 11*60 + 30, "avail_end": 12*60 + 45, "min_duration": 15},         # 11:30 to 12:45
        {"person": "Kimberly", "location": "North Beach", "avail_start": 15*60 + 45, "avail_end": 19*60 + 15, "min_duration": 30}         # 15:45 to 19:15
    ]
    
    num_meetings = len(meetings_data)
    
    # Create an Optimize solver because we need to maximize the number of meetings scheduled.
    opt = Optimize()
    
    # Decision variables for each meeting:
    # scheduled[i] : Bool variable indicating whether the meeting is included.
    # start_vars[i] : Start time of meeting i (in minutes from midnight).
    # end_vars[i] : End time of meeting i.
    # order_vars[i] : Integer representing the order in the itinerary (0 if not scheduled,
    # a positive integer (1...num_meetings) if scheduled; orders for scheduled meetings must be distinct).
    scheduled = [Bool(f"scheduled_{i}") for i in range(num_meetings)]
    start_vars = [Int(f"start_{i}") for i in range(num_meetings)]
    end_vars = [Int(f"end_{i}") for i in range(num_meetings)]
    order_vars = [Int(f"order_{i}") for i in range(num_meetings)]
    
    # Add constraints for each meeting if it is scheduled.
    for i, meeting in enumerate(meetings_data):
        avail_start = meeting["avail_start"]
        avail_end = meeting["avail_end"]
        min_dur = meeting["min_duration"]
        # If scheduled, meeting must happen within the friend's time window.
        opt.add(Implies(scheduled[i], start_vars[i] >= avail_start))
        opt.add(Implies(scheduled[i], end_vars[i] <= avail_end))
        opt.add(Implies(scheduled[i], end_vars[i] - start_vars[i] >= min_dur))
        # If not scheduled, force the order to be 0.
        opt.add(Implies(Not(scheduled[i]), order_vars[i] == 0))
        # If scheduled, order is between 1 and num_meetings.
        opt.add(Implies(scheduled[i], And(order_vars[i] >= 1, order_vars[i] <= num_meetings)))
    
    # There is an initial start fixed at Fisherman's Wharf at 9:00AM (540 minutes).
    # For any meeting that is first in the itinerary, add the travel time from Fisherman's Wharf.
    for i, meeting in enumerate(meetings_data):
        loc = meeting["location"]
        travel_from_start = travel_times[("Fisherman's Wharf", loc)]
        opt.add(Implies(And(scheduled[i], order_vars[i] == 1), start_vars[i] >= 540 + travel_from_start))
    
    # Add pairwise ordering and travel constraints:
    # For any two distinct scheduled meetings, they must have different order numbers.
    # In addition, if meeting i comes before meeting j then travel time from i's location to j's location must be accounted for.
    for i in range(num_meetings):
        for j in range(i+1, num_meetings):
            loc_i = meetings_data[i]["location"]
            loc_j = meetings_data[j]["location"]
            # Ensure if both meetings are scheduled they have distinct order values.
            opt.add(Implies(And(scheduled[i], scheduled[j]), order_vars[i] != order_vars[j]))
            # If meeting i comes before meeting j then:
            travel_ij = travel_times[(loc_i, loc_j)]
            opt.add(Implies(And(scheduled[i], scheduled[j], order_vars[i] < order_vars[j]),
                            start_vars[j] >= end_vars[i] + travel_ij))
            # Conversely, if meeting j comes before meeting i then:
            travel_ji = travel_times[(loc_j, loc_i)]
            opt.add(Implies(And(scheduled[i], scheduled[j], order_vars[j] < order_vars[i]),
                            start_vars[i] >= end_vars[j] + travel_ji))
    
    # Objective: maximize the number of meetings scheduled.
    opt.maximize(Sum([If(scheduled[i], 1, 0) for i in range(num_meetings)]))
    
    if opt.check() == sat:
        m = opt.model()
        # Gather all scheduled meetings with their order.
        scheduled_meetings = []
        for i in range(num_meetings):
            if m.evaluate(scheduled[i]):
                order_val = m.evaluate(order_vars[i]).as_long()
                start_val = m.evaluate(start_vars[i]).as_long()
                end_val = m.evaluate(end_vars[i]).as_long()
                scheduled_meetings.append((order_val, {
                    "action": "meet",
                    "location": meetings_data[i]["location"],
                    "person": meetings_data[i]["person"],
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val)
                }))
        # Sort meetings by their order.
        scheduled_meetings.sort(key=lambda x: x[0])
        itinerary = [entry for (_, entry) in scheduled_meetings]
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()